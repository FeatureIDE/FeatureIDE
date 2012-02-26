/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
package de.ovgu.featureide.featurehouse.errorpropagation;

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
import de.ovgu.featureide.featurehouse.FeatureHouseCorePlugin;

/**
 * Propagates error markers for composed files to sources files.
 * @author Jens Meinicke
 */
public class ErrorPropagation {
	
	/**
	 * A list containing composed files.
	 * These files will be checked for propagation. 
	 */
	private LinkedList<IFile> composedFiles = new LinkedList<IFile>();
	
	/**
	 * The main background job calling the corresponding error propagation class for each file. 
	 */
	private Job job = null;
	
	/**
	 * Propagates error markers for composed files to sources files.<br>
	 * Call <code>addFile(sourceFile)</code> to propagate the markers of the 
	 * given source file, to the corresponding file at the features folder. 
	 */
	public ErrorPropagation() {
		
	}

	/**
	 * Propagates the markers of the given source file, to the corresponding file
	 * at the features folder. 
	 * @param sourceFile The composed file
	 */
	public void addFile(IFile sourceFile) {
		//TODO implement error propagation for all FeatureHouse languages
		if (sourceFile.getFileExtension() == null) {
			return;
		}
		if (sourceFile.getFileExtension().equals("java") || sourceFile.getFileExtension().equals("c") ||
				sourceFile.getFileExtension().equals("h")) {
			if (!composedFiles.contains(sourceFile)) {
				composedFiles.add(sourceFile);
			}
			if (job == null) {
				job = new Job("Propagate problem markers") {
					@Override
					public IStatus run(IProgressMonitor monitor) {
						propagateMarkers();
						return Status.OK_STATUS;
					}
				};
				job.setPriority(Job.DECORATE);
				job.schedule();
			}
			
			if (job.getState() == Job.NONE) {
				job.schedule();
			}
		}
	}

	/**
	 * Calls the corresponding propagation for all files at <code>composedFiles</code>.
	 */
	protected void propagateMarkers() {
		if (composedFiles.isEmpty()) {
			return;
		}
		
		while (!composedFiles.isEmpty()) {
			IFile file = composedFiles.getFirst();
			composedFiles.remove(file);
			ErrorPropagation prop = getErrorPropagation(file);
			if (prop != null) {
				prop.propagateMarkers(file);
			}
		}
	}

	/**
	 * Returns the corresponding error propagation class of the given file.
	 *
	 * @param file 
	 * @return The corresponding <code>ErrorPropagation</code>
	 */
	private ErrorPropagation getErrorPropagation(IFile file) {
		if (file.getFileExtension().endsWith("java")) {
			return new JavaErrorPropagation();
		}
		if (file.getFileExtension().endsWith("c") || file.getFileExtension().endsWith("h")) {
			return new CErrorPropagation();
		} 
		return null;
	}


	/**
	 * Removes the  not composed markers form the given source file and calls <code>propagateMarkers(marker, file)</code>
	 * @param file
	 */
	protected void propagateMarkers(IFile file) {
		if (!file.exists()) {
			return;
		}
		try {
			IMarker[] markers = file.findMarkers(null, true, IResource.DEPTH_INFINITE);
			if (markers.length != 0) {
				LinkedList<IMarker> marker = new LinkedList<IMarker>();
				for (IMarker m : markers) {
					String message = m.getAttribute(IMarker.MESSAGE, null);
					if (message == null || deleteMarker(message)) {
						m.delete();
					} else if (propagateMarker(m)) {
						marker.add(m);
					}
				}
				if (!marker.isEmpty()) {
					propagateMarkers(marker, file);
				}
			}
		} catch (CoreException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Necessary if a marker should not be removed but also should not be propagated.
	 * <br><code>Needs to be implemented by the Subclass.</code>
	 * @param marker
	 * @return <code>false</code> if the marker should not be propagated. 
	 */
	boolean propagateMarker(IMarker marker) {
		return true;
	}


	/**
	 * Necessary if a marker should be removed and also should not be propagated.
	 * <br><code>Needs to be implemented by the Subclass.</code>
	 * @param message
	 * @return <code>true</code> if the marker should not be removed.
	 */
	protected boolean deleteMarker(String message) {
		return false;
	}


	/**
	 * Propagates all markers of the given file
	 * @param markers
	 * @param file
	 */
	private void propagateMarkers(LinkedList<IMarker> markers, IFile file) {
		if (!file.exists()) {
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
		for (FSTFeature f : model.getFeaturesMap().values()) {
			TreeMap<String, FSTClass> z = f.getClasses();
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
		setElementLines(content, fields, methods);

		for (IMarker marker : markers) {
			if (!marker.exists()) {
				continue;
			}
			int markerLine = marker.getAttribute(IMarker.LINE_NUMBER, -1);
			if (markerLine == -1) {
				continue;
			}
			
			boolean propagated = false;
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
			
			if (propagated) {
				continue;
			}
			
			propagateUnsupportedMarker(marker, file);
		}
	}

	/**
	 * Propagates markers outside of methods and fields. 
	 * <br><code>Needs to be implemented by the Subclass.</code>
	 * @param marker
	 * @param file
	 */
	protected void propagateUnsupportedMarker(IMarker marker, IFile file) {
		FeatureHouseCorePlugin.getDefault().logInfo("Marker not propagated: " + marker.getAttribute(IMarker.MESSAGE, ""));
	}

	/**
	 * Sets the composed lines of the given fields and methods.
	 * <br><code>Needs to be implemented by the Subclass.</code>
	 * @param content The content of the composed file
	 * @param fields
	 * @param methods
	 */
	protected void setElementLines(String content,
			LinkedList<FSTField> fields, LinkedList<FSTMethod> methods) {
	}

	/**
	 * Propagates the given marker to the given source line
	 * @param marker The marker to propagate
	 * @param file The features file
	 * @param line The marker line at the features file
	 */
	protected void propagateMarker(IMarker marker, IFile file, int line) {
		if (file != null && file.exists()) {
			Object severity = null;
			String message = marker.getAttribute(IMarker.MESSAGE, "xxx");
			if (message.equals("xxx")) {
				return;
			}
			try {
				severity = marker.getAttribute(IMarker.SEVERITY);
			} catch (CoreException e) {
				severity = IMarker.SEVERITY_ERROR;
			}
			if (!hasSameMarker(message,line,file)) {
				IMarker newMarker = null;
				try {
					newMarker = file.createMarker(FeatureHouseCorePlugin.BUILDER_PROBLEM_MARKER);
					newMarker.setAttribute(IMarker.LINE_NUMBER, line);
					newMarker.setAttribute(IMarker.MESSAGE, message);
					newMarker.setAttribute(IMarker.SEVERITY, severity);
				} catch (CoreException e) {
					FeatureHouseCorePlugin.getDefault().logError(e);
				}
			}
		}
	}

	/**
	 * Checks if the file already the given marker.
	 * @param message
	 * @param line
	 * @param file
	 * @return 
	 */
	private boolean hasSameMarker(String message, int line, IFile file) {
		try {
			IMarker[] markers = file.findMarkers(null, true, IResource.DEPTH_INFINITE);
			for (IMarker m : markers) {
				if (m.getAttribute(IMarker.LINE_NUMBER, -1) == line) {
					if (m.getAttribute(IMarker.MESSAGE, "xxx").equals(message)) {
						return true;
					}
				}
			}
		} catch (CoreException e) {

		}
		return false;
	}

	/**
	 * Count the lines of the given substring.
	 */
	protected int countLines(String substring) {
		return (substring + " ").split("[\n]").length;
	}

	/**
	 * 
	 * @param file
	 * @return The content of the given file
	 */
	private String getFileContent(IFile file) {
		Scanner scanner = null;
		try {
			scanner = new Scanner(file.getRawLocation().toFile());
			StringBuffer buffer = new StringBuffer();
			if (scanner.hasNext()) {
				while (scanner.hasNext()) {
					buffer.append(scanner.nextLine());
					buffer.append('\n');
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
