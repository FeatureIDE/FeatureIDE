/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package featureide.core.builder;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.Map;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;

import featureide.core.CorePlugin;
import featureide.core.IFeatureProject;

/**
 * 
 * TODO description
 * 
 * @author Janet Feigenspan
 * @deprecated
 */
public class FeatureCPPBuilder extends IncrementalProjectBuilder {

	private IFeatureProject featureProject;
	private String sourcePath;
	private String equationFile;
	private String fcppPath;

	public static final String BUILDER_ID = CorePlugin.PLUGIN_ID + ".featureCPPBuilder";

	/**
	 * TODO adjust, when fc++ can handle other directories some Variables for
	 * Call to Feature C++ and Cygwin
	 */
	private static final String fcpp = "fc++.exe";
	private static final String m_gpp = "-gpp";

	private static final String gpp = "g++ ";
	private static final String output = "\\.output.";
	private static final String exe = ".exe";

	private ArrayList<ErrorMessage> errorMessage = new ArrayList<ErrorMessage>();

	private boolean featureProjectLoaded() {
		if (featureProject != null)
			return true;

		featureProject = CorePlugin.getProjectData(getProject());
		if (featureProject == null)
			return false;

		return true;
	}

	// TODO adjust, when fc++ can handle other directories
	protected void clean(IProgressMonitor monitor) throws CoreException {

		// String equationFile =
		// featureProject.getCurrentEquationFile().getName();
		CorePlugin.getDefault().logInfo("clean");

		errorMessage.clear();

		featureProject.deleteBuilderMarkers(featureProject.getSourceFolder(),
				IResource.DEPTH_INFINITE);

		featureProject.getBinFolder().getFolder(equationFile).delete(true,
				monitor);
		featureProject.getBuildFolder().getFolder(equationFile).delete(true,
				monitor);

		featureProject.getBuildFolder().refreshLocal(IResource.DEPTH_INFINITE,
				monitor);
		featureProject.getBinFolder().refreshLocal(IResource.DEPTH_INFINITE,
				monitor);
	}

	@SuppressWarnings("unchecked")
	protected IProject[] build(int kind, Map args, IProgressMonitor monitor)
			throws CoreException {

		if (!featureProjectLoaded()) {
			return null;
		}

		// TODO adjust, when fc++ can handle other directories
		equationFile = getCPPEquationFile();

		// clean the project before build
		featureProject.deleteBuilderMarkers(getProject(),
				IResource.DEPTH_INFINITE);
		try {
			// TODO replace by change listener, that removes derived resources
			// when their non-derived encounter part is deleted
			clean(monitor);
		} catch (CoreException e) {
			e.printStackTrace();
		}

		sourcePath = featureProject.getSourcePath();
		fcppPath = featureProject.getProject().getLocation().toOSString();

		// call to fc++
		int exitFCPP = doFcpp();

		// call to c++-compiler (cygwin), if no errors occured
		if (exitFCPP == 0)
			doGpp();

		// create the builder markers for all occured errors
		Iterator<ErrorMessage> iterateErrors = errorMessage.iterator();
		while (iterateErrors.hasNext()) {
			createBuilderMarkers(iterateErrors.next());
		}

		return null;
	}

	/**
	 * creates the builder markers from the global errorMessage object
	 * 
	 * @param errorMessage
	 *            the error message for the builder marker
	 */
	private void createBuilderMarkers(ErrorMessage errorMessage) {
		if (errorMessage != null) {
			IPath projectPath = featureProject.getProject().getLocation();
			IPath filePath = new Path(errorMessage.getFile());
			if (projectPath.isPrefixOf(filePath)) {
				filePath = filePath.removeFirstSegments(projectPath
						.segmentCount());
			}

			// check the severity of the problem
			int error = 2;
			if (errorMessage.getType() != null) {
				if (errorMessage.getType().equalsIgnoreCase("error"))
					error = IMarker.SEVERITY_ERROR;
				else if (errorMessage.getType().equalsIgnoreCase("warning"))
					error = IMarker.SEVERITY_WARNING;
				else if (errorMessage.getType().equalsIgnoreCase("info"))
					error = IMarker.SEVERITY_INFO;
			}

			featureProject.createBuilderMarker(getProject().getFile(filePath),
					errorMessage.getMessage(), errorMessage.getLine(), error);
		}
	}

	/**
	 * call the the c++-compiler for compiling the composed project
	 */
	private int doGpp() {
		try {
			// delete current exe-file
			featureProject.getBinFolder().getFile(equationFile + exe).delete(
					true, null);

			// call c++-compiler
			ProcessBuilder procGpp = new ProcessBuilder(new String[] { gpp,
					sourcePath + output + equationFile + "/*.cpp", "-o",
					featureProject.getBinPath() + "\\" + equationFile + exe });
			Process p = procGpp.start();

			// get error output from c++-compiler
			StreamGobbler outputGobbler = new StreamGobbler(p.getErrorStream(),
					"OUTPUT");
			outputGobbler.start();

			// wait, until c++-compiler has terminated
			int exitValGpp = -1;
			exitValGpp = p.waitFor();
			System.out.println("ExitValue g++: " + exitValGpp);

			// refresh workspace
			featureProject.getBinFolder().refreshLocal(
					IResource.DEPTH_INFINITE, null);

			// parse the error messages of the c++-compiler
			Iterator<String> iterator = outputGobbler.errors.iterator();
			while (iterator.hasNext()) {
				errorMessage.add(parseCPPErrors(iterator.next()));
			}
			return exitValGpp;
		} catch (CoreException e1) {
			System.out
					.println("Could not delete executable. Current executable may be incorrect.");
			e1.printStackTrace();
		} catch (IOException e) {
			CorePlugin.getDefault().logInfo("Could not run c++-compiler");
			e.printStackTrace();
		} catch (InterruptedException e) {
			System.out
					.println("c++-compiler did probably not end without error");
			e.printStackTrace();
		}
		return -1;
	}

	private ErrorMessage parseCPPErrors(String cppErrorMessage) {
		ErrorMessage errMsg = new ErrorMessage();
		// TODO parse the first line of the error message...
		if (cppErrorMessage.indexOf(":") == 1) {
			// get the file
			String file = cppErrorMessage.substring(0, cppErrorMessage
					.indexOf(": "));
			if (file.lastIndexOf(":") > 1) {
				file = file.substring(0, file.lastIndexOf(":"));
			}
			errMsg.setFile(file);
			// System.out.println("cppErr: " + errMsg.getFile());

			// get the line number
			String lineNumber = cppErrorMessage.substring(0, cppErrorMessage
					.indexOf(": "));
			if (lineNumber.lastIndexOf(":") > 1) {
				lineNumber = lineNumber.substring(
						lineNumber.lastIndexOf(":") + 1, lineNumber.length());
				errMsg.setLine(Integer.parseInt(lineNumber));
			}
			// System.out.println("cppLine: " + errMsg.getLine());

			// get the message
			String msg = cppErrorMessage.substring(cppErrorMessage
					.indexOf(": ") + 2, cppErrorMessage.length());
			errMsg.setMessage(msg);
			// System.out.println("cppMsg: " + errMsg.getMessage());
			return errMsg;
		}
		return null;
	}

	/**
	 * call to fc++ for composing the layers
	 * 
	 * @return the exit value of fc++, or -1, if it could not be obtained
	 */
	private int doFcpp() {
		try {
			// delete current output-folder
			IFolder folder = featureProject.getSourceFolder().getFolder(
					output + equationFile);
			folder.delete(true, null);

			// call fc++
			ProcessBuilder procGpp = new ProcessBuilder(new String[] {
					fcppPath + fcpp, m_gpp, sourcePath + "\\" + equationFile });
			procGpp = procGpp.redirectErrorStream(true);
			Process p = procGpp.start();

			// grab the output of fc++ so that it can terminate normally
			StreamGobbler errorGobbler = new StreamGobbler(p.getErrorStream(),
					"ErrorFcpp");
			errorGobbler.start();
			StreamGobbler outputGobbler = new StreamGobbler(p.getInputStream(),
					"OUTPUTFcpp");
			outputGobbler.start();

			int exitValFcpp;
			CorePlugin.getDefault().logInfo("running fc++...");
			exitValFcpp = p.waitFor();
			CorePlugin.getDefault().logInfo("ExitValue Process fc++: " + exitValFcpp);
			
			// refresh workspace
			folder = featureProject.getSourceFolder();
			CorePlugin.getDefault().logInfo("Folder: " + folder);
			folder.refreshLocal(IResource.DEPTH_INFINITE, null);

			// parse the error messages from fc++ (xml-file)
			createFPPErrorMessages((IFolder) featureProject.getSourceFolder()
					.findMember(output + equationFile));

			return exitValFcpp;
		} catch (CoreException e) {
			CorePlugin.getDefault().logInfo("Could not delete outputFolder. "
					+ "Make sure that it is not used by any other program. "
					+ "Fc++-build is now incorrect. ");
			e.printStackTrace();
		} catch (InterruptedException e) {
			CorePlugin.getDefault().logInfo("fc++ did probably not end without error");
			e.printStackTrace();
		} catch (IOException e) {
			CorePlugin.getDefault().logInfo("Could not run fc++");
			e.printStackTrace();
		}
		return -1;

	}

	/**
	 * finds the xml-log-file, creates error messages and stores them globally
	 * 
	 * @param resource
	 *            contains the output dir, that fc++ generates
	 */
	private void createFPPErrorMessages(IFolder resource) {
		if (resource != null) {
			try {

				// find the xml-log-file and create a list of
				// ErrorMessage-Objects
				IResource[] members = resource.members();
				for (int i = 0; i < members.length; i++) {
					if (members[i].getFileExtension().equals("xml")) {
						errorMessage.addAll(new ErrorLogParser(members[i]
								.getRawLocation().toString())
								.createErrorMessages());
						break;
					}
				}

			} catch (CoreException e) {
				e.printStackTrace();
			}
		}
	}

	/**
	 * TODO adjust/delete, when fc++ can handle other directories
	 * 
	 * @return
	 */
	private String getCPPEquationFile() {
		IFolder srcFolder = featureProject.getSourceFolder();
		IResource[] members;
		try {
			members = srcFolder.members();
			for (int i = 0; i < members.length; i++) {
				if (members[i].getFileExtension() != null
						&& members[i].getFileExtension().equals("equation")) {
					String s = members[i].toString().replace('/', '\\');
					return s.substring(s.lastIndexOf('\\') + 1, s
							.lastIndexOf('.'));
				}
			}
		} catch (CoreException e) {
			e.printStackTrace();
		}
		return null;
	}

}
