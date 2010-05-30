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
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.featurecpp.FeatureCppCorePlugin;

/**
 * Composes FeatureC++ files. Compiles C++ Files.
 * 
 * @author Tom Brosch
 * @author Jens Meinicke
 */
public class FeatureCppWrapper {

	final String featureCppExecutableName;

	private String sourceFolder = null;

	private String buildFolder = null;

	private String binFolder = null;

	private String projectName = "";

	private IFolder binDirectory = null;

	private IFolder buildDirectory = null;

	public FeatureCppWrapper(String featureCppExecutablePath) {
		this.featureCppExecutableName = featureCppExecutablePath;
	}

	public void initialize(IFolder source, IFolder build, IFolder bin,
			String project) {
		sourceFolder = source.getRawLocation().toOSString();
		buildFolder = build.getRawLocation().toOSString();
		binFolder = bin.getRawLocation().toOSString();
		projectName = project;
		binDirectory = bin;
		buildDirectory = build;
	}

	public void compose(IFile equation) {
		assert (equation != null && equation.exists()) : "Equation file does not exist";
		String equationName = equation.getName();
		if (equationName.contains(".")) {
			equationName = equationName.substring(0, equationName.indexOf('.'));
		}

		IFolder folder = binDirectory.getFolder(equationName);
		try {
			if (!folder.exists())
				folder.create(false, true, null);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		IFolder folder2 = buildDirectory.getFolder(equationName);
		try {
			if (!folder2.exists())
				folder2.create(false, true, null);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		LinkedList<String> command = new LinkedList<String>();
		command.add(featureCppExecutableName);
		command.add("-o=" + buildFolder + "\\" + equationName);
		command.add("-s=" + sourceFolder);
		command.add("-gpp");
		command.add(equation.getRawLocation().toOSString());
		try {
			process(command);
			compile(equation);
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

	public void compile(IFile equation) throws IOException {
		String equationName = equation.getName();
		if (equationName.contains(".")) {
			equationName = equationName.substring(0, equationName.indexOf('.'));
		}

		try {
			buildDirectory.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			FeatureCppCorePlugin.getDefault().logError(e);
		}

		LinkedList<String> command2 = new LinkedList<String>();
		command2.add("g++");
		command2.add("-o" + binFolder + "\\" + equationName + "\\"
				+ projectName + "-" + equationName + ".exe");

		try {
			for (IResource res : buildDirectory.getFolder(equationName)
					.members()) {
				String fileName = res.getName();
				if (fileName.endsWith(".cpp")) {
					LinkedList<String> command = new LinkedList<String>();
					command.add("g++");
					command.add("-O3");
					command.add("-Wall");
					command.add("-c");
					command.add("-fmessage-length=0");
					String file = binFolder
							+ "\\"
							+ equationName
							+ "\\"
							+ res.getName().substring(0,
									res.getName().length() - 4) + ".o";
					command.add("-o" + file);
					command2.add(file);
					command.add(res.getLocation().toOSString());
					process(command);
				}
			}
		} catch (CoreException e) {
			FeatureCppCorePlugin.getDefault().logError(e);
		}
		process(command2);
		try {
			binDirectory.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			FeatureCppCorePlugin.getDefault().logError(e);
		}
	}
}
