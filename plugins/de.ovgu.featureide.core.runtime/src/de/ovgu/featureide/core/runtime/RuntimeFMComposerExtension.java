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
package de.ovgu.featureide.core.runtime;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.UnsupportedEncodingException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashMap;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.runtime.activator.RuntimeCorePlugin;
import de.ovgu.featureide.fm.core.FMComposerExtension;

/**
 * Class for handling renaming events of features within the model.
 *
 * @author Kai Wolf
 * @author Matthias Quaas
 *
 */
public class RuntimeFMComposerExtension extends FMComposerExtension {

	private static String ORDER_PAGE_MESSAGE = "FeatureIDE projects based on runtime variability do not support any order.";

	@Override
	public String getErrorMessage() {
		return super.getErrorMessage();
	}

	@Override
	public String getOrderPageMessage() {
		return ORDER_PAGE_MESSAGE;
	}

	@Override
	public boolean hasFeatureOrder() {
		return false;
	}

	/**
	 * Check for valid java identifier
	 */
	@Override
	protected boolean isValidFeatureNameComposerSpecific(String s) {
		// An empty or null string cannot be a valid identifier
		if ((s == null) || (s.length() == 0)) {
			return false;
		}

		final char[] c = s.toCharArray();
		if (!Character.isJavaIdentifierStart(c[0])) {
			return false;
		}

		for (int i = 1; i < c.length; i++) {
			if (!Character.isJavaIdentifierPart(c[i])) {
				return false;
			}
		}

		return true;
	}

	/**
	 * Actual handling of renaming.
	 */
	@Override
	public boolean performRenaming(final String oldName, final String newName, final IProject project) {

		final ArrayList<FeatureLocation> locations = new ArrayList<FeatureLocation>();

		// get FeatureLocation objects with the given oldName as feature name
		for (final FeatureLocation loc : RuntimeParameters.featureLocs) {
			if (loc.getFeatureName().equals(oldName)) {
				locations.add(loc);
			}
		}
		// only load and parse each class file once
		final HashMap<String, String[]> processedClassFiles = new HashMap<String, String[]>();

		for (final FeatureLocation loc : locations) {
			String[] oldClassStringArray = null;
			final String classPath = loc.getOSPath();
			final int lineNumber = loc.getStartLineNum();

			// if the class has not already been loaded, load it
			if (!processedClassFiles.containsKey(classPath)) {

				try {
					final IFile classFile = loc.getClassFile();
					final InputStream oldClassStream = classFile.getContents();

					final StringBuilder inputStringBuilder = new StringBuilder();
					BufferedReader bufferedReader = null;

					bufferedReader = new BufferedReader(new InputStreamReader(oldClassStream, "UTF-8"));

					String line = bufferedReader.readLine();
					while (line != null) {
						inputStringBuilder.append(line);
						inputStringBuilder.append('\n');
						line = bufferedReader.readLine();
					}
					oldClassStringArray = inputStringBuilder.toString().split("\\n");
					processedClassFiles.put(classPath, oldClassStringArray);

				} catch (final UnsupportedEncodingException e) {
					RuntimeCorePlugin.getDefault().logError(e);
				} catch (final IOException e) {
					RuntimeCorePlugin.getDefault().logError(e);
				} catch (final CoreException e) {
					RuntimeCorePlugin.getDefault().logError(e);
				}
				// else use the one in the map
			} else {
				oldClassStringArray = processedClassFiles.get(classPath);
			}
			oldClassStringArray[lineNumber - 1] = oldClassStringArray[lineNumber - 1].replace(RuntimeParameters.GET_PROPERTY_METHOD + "(\"" + oldName + "\")",
					RuntimeParameters.GET_PROPERTY_METHOD + "(\"" + newName + "\")");

			final StringBuilder newClassString = new StringBuilder();
			for (int i = 0; i < oldClassStringArray.length; i++) {
				if (i != 0) {
					newClassString.append(System.lineSeparator());
				}
				newClassString.append(oldClassStringArray[i]);
			}

			final InputStream newClassStream = new ByteArrayInputStream(newClassString.toString().getBytes(StandardCharsets.UTF_8));
			try {
				loc.getClassFile().setContents(newClassStream, IResource.FORCE, null);
			} catch (final CoreException e) {
				RuntimeCorePlugin.getDefault().logError(e);
			}
			loc.setFeatureName(newName);
		}

		return true;

	}

}
