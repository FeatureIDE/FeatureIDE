/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.featurehouse;

import java.io.FileNotFoundException;
import java.util.LinkedList;
import java.util.Scanner;
import java.util.TreeMap;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;

/**
 * Propagates error markers for composed files to sources files.
 * 
 * @author Jens Meinicke
 */
public class ErrorPropagation {
	
	public ErrorPropagation(final IFile file) {
		if (!file.getFileExtension().equals("java")) {
			// TODO implement error propagation for all supported languages
			return;
		}
		try {
			final IMarker[] markers = file.findMarkers(null, true, IResource.DEPTH_ZERO);
			if (markers.length == 0) {
				return;
			}
			Job job = new Job("Propagate problem markers") {
				@Override
				public IStatus run(IProgressMonitor monitor) {
					propagateMarkers(markers, file);
					return Status.OK_STATUS;
				}
			};
			job.setPriority(Job.DECORATE);
			job.schedule();
		} catch (CoreException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		}
	}
	
	/**
	 * Propagates all markers of the given file
	 */
	private void propagateMarkers(IMarker[] markers, IFile file) {
		if (!file.exists() || markers.length == 0) {
			return;
		}
		String content = getFileContent(file);
		LinkedList<FSTField> fields = new LinkedList<FSTField>();
		LinkedList<FSTMethod> methods = new LinkedList<FSTMethod>();
		IFeatureProject project = CorePlugin.getFeatureProject(file);
		if (project == null) {
			return;
		}
		FSTModel model = project.getFSTModel();
		if (model == null) {
			return;
		}
		for (FSTFeature f : model.features.values()) {
			TreeMap<String, FSTClass> z = f.classes;
			if (z.containsKey(file.getName())) {
				FSTClass c = z.get(file.getName());
				for (FSTField field : c.getFields()) {
					fields.add(field);
				}
				for (FSTMethod method : c.getMethods()) {
					methods.add(method);
				}
			}
		}
		setElementLines(content, file, fields, methods);

		for (IMarker marker : markers) {
			if (!marker.exists()) {
				continue;
			}
			boolean propagated = false;
			int markerLine = marker.getAttribute(IMarker.LINE_NUMBER, -1);
			
			for (FSTField f : fields) {
				if (markerLine >= f.getComposedLine()
						&& markerLine <= f.getComposedLine()
								+ (f.getEndLine() - f.getBeginLine())) {
					propagateMarker(marker, f.getOwnFile(), f.getBeginLine()
							+ markerLine - f.getComposedLine());
					propagated = true;
					break;
				}
			}

			if (propagated) {
				continue;
			}

			for (FSTMethod m : methods) {
				if (markerLine >= m.getComposedLine() && 
						markerLine <= m.getComposedLine() + (m.getEndLine() - m.getBeginLine())) {
					propagateMarker(marker, m.getOwnFile(), m.getBeginLine() + markerLine - m.getComposedLine());
					propagated = true;
					break;
				}
			}
		}
	}

	/**
	 * Propagates the marker to the source line
	 */
	private void propagateMarker(IMarker marker, IFile file, int line) {
		if (file != null && file.exists()) {
			try {
				IMarker newMarker = file.createMarker(FeatureHouseCorePlugin.BUILDER_PROBLEM_MARKER);
				if (!newMarker.exists()) {
					return;
				}
				newMarker.setAttribute(IMarker.LINE_NUMBER, line);
				newMarker.setAttribute(IMarker.MESSAGE, marker.getAttribute(IMarker.MESSAGE));
				newMarker.setAttribute(IMarker.SEVERITY, marker.getAttribute(IMarker.SEVERITY));
				marker.delete();
			} catch (CoreException e) {
				FeatureHouseCorePlugin.getDefault().logError(e);
			}
		}
		
	}

	/**
	 * Sets all composed lines to all methods and fields
	 */
	private void setElementLines(String content, IFile file, LinkedList<FSTField> fields, LinkedList<FSTMethod> methods) {
		for (FSTField f : fields) {
			if (f.getBody() == null) {
				continue;
			}
			int i = content.indexOf(f.getBody());
			int line = countLines(content.substring(0, i));
			f.setComposedLine(line);
		}

		content = content.replaceAll("__wrappee__\\w*\\s*", "");
		content = content.replaceAll("  ", " ");

		for (FSTMethod m : methods) {
			if (m.getBody() == null) {
				continue;
			}
			int i = -1;
			if (m.isConstructor) {
				String body = m.getBody().substring(m.getBody().indexOf("{") + 1);
				body = body.replaceAll("  ", " ");
				body = body.substring(0, body.lastIndexOf("}"));
				i = content.indexOf(body);
			} else {
				String body = m.getBody();
				body = body.replaceAll("  ", " ");
				body = body.replaceFirst("\\s*\\(", "(");
				if (body.startsWith("public")) {
					body = body.replaceFirst("public", "");
				} else if (body.startsWith("protected")) {
					body = body.replaceFirst("protected", "");
				}
				if (body.contains("original")) {
					body = body.replaceFirst("original", m.methodName);
				}
				i = content.indexOf(body);
				System.out.println();
			}
			if (i != -1) {
				int line = countLines(content.substring(0, i));
				m.setLine(line);
			}
		}
	}

	private int countLines(String substring) {
		return substring.split("[\n]").length;
	}

	private String getFileContent(IFile file) {
		Scanner scanner = null;
		try {
			scanner = new Scanner(file.getRawLocation().toFile());
			StringBuffer buffer = new StringBuffer();
			if (scanner.hasNext()) {
				while (scanner.hasNext()) {
					buffer.append(scanner.nextLine());
					buffer.append("\r\n");
				}
			}
			return buffer.toString();
		} catch (FileNotFoundException e) {
			CorePlugin.getDefault().logError(e);
		} finally {
			if (scanner != null)
				scanner.close();
		}
		return "";
	}
}
