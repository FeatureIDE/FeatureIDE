/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 *
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.featurehouse.errorpropagation;

import java.io.FileNotFoundException;
import java.util.Collection;
import java.util.LinkedList;
import java.util.Scanner;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.functional.Functional.IFunction;

/**
 * Propagates errors for <code>FeatureHouse</code> Java files.
 *
 * @author Jens Meinicke
 * @author Marcus Pinnecke (Feature Interface)
 */
public class JavaErrorPropagation extends ErrorPropagation {

	private static final String REMOVED_LINES_2 = "2Lines";
	private static final String REMOVED_LINES_4 = "4Lines";

	// Java 1.4 exclusions
	private static final String RAW_TYPE = "raw type";
	private static final String GENERIC_TYPE = "generic type";
	private static final String TYPE_SAFETY = "Type safety";
	// private static final String IMPORT = THE_IMPORT;

	private static final String TASK = "org.eclipse.jdt.core.task";
	private Collection<String> layerNames = null;

	protected JavaErrorPropagation(IFeatureProject featureProject) {
		super(featureProject);
	}

	/**
	 *
	 * Sets all composed lines to all methods and fields
	 */
	@Override
	protected void setElementLines(String content, LinkedList<FSTField> fields, LinkedList<FSTMethod> methods) {
		for (final FSTField f : fields) {
			if (f.getBody() == null) {
				continue;
			}
			final int i = content.indexOf(f.getBody());
			if (i == -1) {
				continue;
			}
			final int line = countLines(content.substring(0, i));
			f.setComposedLine(line);
		}
		content = content.replaceAll("__wrappee__\\w*\\s*", "");

		content = content.replaceAll("[^{]if \\(!FeatureModel.\\w*\\) \\{[^}]*\\}\\n", REMOVED_LINES_4);
		content = content.replaceAll("[^{]if \\(!FeatureModel.\\w*\\)[^;]*;\\n", REMOVED_LINES_2);

		content = content.replaceAll("/\\*@", "");
		content = content.replaceAll("@\\*/", "");
		while (content.contains("  ")) {
			content = content.replaceAll("  ", " ");
		}
		content = content.replaceAll("\t", "");
		while (content.contains(" (")) {
			content = content.replaceAll(" \\(", "(");
		}
		for (final FSTMethod method : methods) {
			if (method.getBody() == null) {
				continue;
			}
			if (method.isConstructor()) {
				int i = -1;
				String body = method.getBody().substring(method.getBody().indexOf('{') + 1);
				while (body.contains("  ")) {
					body = body.replaceAll("  ", " ");
				}
				body = body.replaceAll("\t", "");
				while (body.contains(" (")) {
					body = body.replaceAll(" \\(", "(");
				}
				body = body.replaceAll("\r\n", "\n");
				body = body.substring(0, body.lastIndexOf('}'));
				i = content.indexOf(body);
				if (i != -1) {
					final int line = countLines(content.substring(0, i));
					method.setLine(line);
				}
			} else {
				final boolean success = findComposedLine(method, content, true);
				if (!success) {
					findComposedLine(method, content, false);
				}
			}
		}
	}

	/**
	 * Sets the composed line for the given method.
	 *
	 * @param method The method
	 * @param content The composed file content.
	 * @param replaceOriginal Defines whether the original call should be replaced by the method call.
	 * @return <code>true</code> if the composed line was found.
	 */
	private boolean findComposedLine(FSTMethod method, final String content, boolean replaceOriginal) {
		String body = method.getBody();
		while (body.contains("  ")) {
			body = body.replaceAll("  ", " ");
		}
		body = body.replaceAll("\t", "");
		while (body.contains(" (")) {
			body = body.replaceAll(" \\(", "(");
		}
		if (body.startsWith("public")) {
			body = body.replaceFirst("public", "");
		} else if (body.startsWith("protected")) {
			body = body.replaceFirst("protected", "");
		}
		body = body.replaceAll("\r\n", "\n");
		if (replaceOriginal) {
			body = body.replaceAll("original\\(", method.getName() + "(");
			body = body.replaceAll("original\\s*\\(", method.getName() + " (");
		}
		final StringBuilder stringBuilder = new StringBuilder();
		int lineCounter = 1;
		int methodOverhead = 0;
		boolean found = false;
		for (final String line : content.split("[\n]")) {
			stringBuilder.append(line);
			stringBuilder.append("\n");
			final String actualContent = stringBuilder.toString();
			if (actualContent.replaceAll(REMOVED_LINES_4, "").replaceAll(REMOVED_LINES_2, "").contains(body)) {
				found = true;
				if (!actualContent.contains(body)) {
					if (actualContent.replaceAll(REMOVED_LINES_4, "").contains(body)) {
						methodOverhead = 4;
					} else {
						methodOverhead = 2;
					}
				}
				break;
			}
			if (line.startsWith(REMOVED_LINES_4)) {
				lineCounter += 4;
			} else if (line.startsWith(REMOVED_LINES_2)) {
				lineCounter += 2;
			}

			lineCounter++;

		}
		if (found) {
			method.setComposedLine(lineCounter - ((method.getEndLine() - method.getLine()) + methodOverhead));
		}
		return found;

	}

	@Override
	protected boolean deleteMarker(String message) {
		return (message.contains(RAW_TYPE) || message.contains(TYPE_SAFETY) || message.contains(GENERIC_TYPE)
		// ||message.contains(IMPORT)
		);
	}

	@Override
	protected boolean propagateMarker(IMarker m) {
		try {
			return !(TASK.equals(m.getType()));
		} catch (final CoreException e) {}
		return super.propagateMarker(m);
	}

	@Override
	protected void propagateUnsupportedMarker(IMarker marker, IFile file) {
		final int markerLine = marker.getAttribute(IMarker.LINE_NUMBER, -1);
		final String lineContent = getLineContent(file, markerLine);
		final LinkedList<IFile> featureFiles = getFeatureFiles(file);
		for (final IFile featureFile : featureFiles) {
			final int newMarkerLine = getLine(featureFile, lineContent);
			if (newMarkerLine != -1) {
				propagateMarker(marker, featureFile, newMarkerLine);
				return;
			}
		}
	}

	/**
	 * Checks if the given file contains a line with the given content.
	 *
	 * @param lineContent the content to look for
	 * @return The line of the content or <code>-1</code> if the does not contain the content.
	 */
	private int getLine(IFile file, String lineContent) {
		Scanner scanner = null;
		lineContent = correctString(lineContent);
		try {
			int line = 1;
			scanner = new Scanner(file.getRawLocation().toFile(), "UTF-8");
			while (scanner.hasNext()) {
				String content = scanner.nextLine();
				content = correctString(content);
				if (content.endsWith(lineContent)) {
					return line;
				}
				line++;
			}
		} catch (final FileNotFoundException e) {
			CorePlugin.getDefault().logError(e);
		} finally {
			if (scanner != null) {
				scanner.close();
			}
		}
		return -1;
	}

	/**
	 * Corrects the given string to avoid changes by the <code>FeatureHouse</code> composer.
	 */
	private String correctString(String string) {
		while (string.contains("  ")) {
			string = string.replaceAll("  ", " ");
		}
		if (string.endsWith("{")) {
			string = string.substring(0, string.indexOf('{'));
		}
		if (string.endsWith(" ")) {
			string = string.substring(0, string.length() - 1);
		}
		return string;
	}

	/**
	 * @param file A composed file
	 * @return A list containing all corresponding feature files
	 */
	private LinkedList<IFile> getFeatureFiles(IFile file) {
		final IFeatureProject project = CorePlugin.getFeatureProject(file);
		if (project == null) {
			return null;
		}

		if (layerNames == null) {
			final IFeatureModel model = project.getFeatureModel();
			if (model.isFeatureOrderUserDefined()) {
				layerNames = model.getFeatureOrderList();
			} else {
				layerNames = Functional.toList(Functional.map(model.getFeatures(), new IFunction<IFeature, String>() {

					@Override
					public String invoke(IFeature t) {
						return t.getName();
					}

				}));
			}
		}

		final LinkedList<IFile> featureFiles = new LinkedList<IFile>();
		final FSTModel fstModel = project.getFSTModel();
		final FSTClass c = fstModel.getClass(fstModel.getAbsoluteClassName(file));
		for (final FSTRole role : c.getRoles()) {
			featureFiles.add(role.getFile());
		}
		return featureFiles;
	}

	/**
	 *
	 * @param line The line to lock for
	 * @return the content at the given line of the file
	 */
	private String getLineContent(IFile file, int line) {
		Scanner scanner = null;
		try {
			scanner = new Scanner(file.getRawLocation().toFile(), "UTF-8");
			if (scanner.hasNext()) {
				while (scanner.hasNext()) {
					if (line == 1) {
						return scanner.nextLine();
					}
					line--;
					scanner.nextLine();
				}
			}
		} catch (final FileNotFoundException e) {
			CorePlugin.getDefault().logError(e);
		} finally {
			if (scanner != null) {
				scanner.close();
			}
		}
		return "";
	}

}
