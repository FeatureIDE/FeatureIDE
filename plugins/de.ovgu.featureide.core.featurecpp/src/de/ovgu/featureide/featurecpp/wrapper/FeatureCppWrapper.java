/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.featurecpp.wrapper;


import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.featurecpp.FeatureCppCorePlugin;

/**
 * Composes FeatureC++ files.
 * 
 * @author Tom Brosch
 * @author Jens Meinicke
 */
public class FeatureCppWrapper {

	final String featureCppExecutableName;

	private String sourceFolder = null;

	private String buildFolder = null;

	private IFolder buildDirectory = null;

	public FeatureCppWrapper(String featureCppExecutablePath) {
		this.featureCppExecutableName = featureCppExecutablePath;
	}

	public void initialize(IFolder source, IFolder build) {
		sourceFolder = source.getRawLocation().toOSString();
		buildFolder = build.getRawLocation().toOSString();
		buildDirectory = build;
	}

	public void compose(IFile equation) {
		assert (equation != null && equation.exists()) : "Equation file does not exist";
		String equationName = equation.getName();
		if (equationName.contains(".")) {
			equationName = equationName.substring(0, equationName.indexOf('.'));
		}
		IFolder folder2 = buildDirectory;
		try {
			if (!folder2.exists())
				folder2.create(false, true, null);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		LinkedList<String> command = new LinkedList<String>();
		command.add(featureCppExecutableName);
		command.add("-o=" + buildFolder);
		command.add("-s=" + sourceFolder);
		command.add("-gpp");
		command.add(equation.getRawLocation().toOSString());
		// TODO configuration extension must be .equation
		try {
			process(command);
		} catch (IOException e) {
			FeatureCppCorePlugin.getDefault().logError(e);
		}
	}

	private void process(LinkedList<String> command) throws IOException {
		ProcessBuilder processBuilder = new ProcessBuilder(command);
		try {
			Process process = processBuilder.start();
			BufferedReader input = new BufferedReader(new InputStreamReader(
					process.getInputStream()));
			BufferedReader error = new BufferedReader(new InputStreamReader(
					process.getErrorStream()));
			boolean x = true;
			while (x) {
				try {
					String line;
					while ((line = input.readLine()) != null) {}
					while ((line = error.readLine()) != null)
						FeatureCppCorePlugin.getDefault().logInfo(line);
					int exitValue = process.exitValue();
					if (exitValue != 0) {
						throw new IOException(
								"The process doesn't finish normally (exit="
										+ exitValue + ")!");
					}
					x = false;
				} catch (IllegalThreadStateException e) {
				}
			}
		} catch (IOException e) {
			FeatureCppCorePlugin.getDefault().logError(e);
		}	
	}

}
