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
package de.ovgu.featureide.cmake.wrapper;

import static de.ovgu.featureide.fm.core.localization.StringTable.CONFIGURATION_FILE_DOES_NOT_EXIST;
import static de.ovgu.featureide.fm.core.localization.StringTable.GPP;
import static de.ovgu.featureide.fm.core.localization.StringTable.IS_NOT_AN_ABSOLUTE_PATH_;
import static de.ovgu.featureide.fm.core.localization.StringTable.IS_NO_VALID_PATH_;
import static de.ovgu.featureide.fm.core.localization.StringTable.LINUX;
import static de.ovgu.featureide.fm.core.localization.StringTable.PROPAGATE_PROBLEM_MARKERS_FOR;
import static de.ovgu.featureide.fm.core.localization.StringTable.RESTRICTION;
import static de.ovgu.featureide.fm.core.localization.StringTable.SEE;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.net.URL;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.util.AbstractList;
import java.util.LinkedList;

import org.eclipse.cdt.core.CCorePlugin;
import org.eclipse.cdt.core.ConsoleOutputStream;
import org.eclipse.cdt.core.resources.IConsole;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.MessageBox;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;
import org.eclipse.ui.internal.util.BundleUtility;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.cmake.CMakeCorePlugin;
import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.fm.core.ModelMarkerHandler;

/**
 * Composes FeatureC++ files.
 * 
 * @author Tom Brosch
 * @author Jens Meinicke
 */
@SuppressWarnings(RESTRICTION)
public class CMakeWrapper {
	public static final String CMAKE_COMMAND = "cmake";
	public static final String CMAKE_GENERATOR_OPT = "-G";
	public static final String CMAKE_CACHE_OPT = "-C";
	public static final String CMAKE_GENERATOR = "MinGW Makefiles";

	private String sourceFolder = null;
	
	private IFolder source = null;

	private String buildFolder = null;

	private IFolder buildDirectory = null;
	
	private int version = 7;

	public CMakeWrapper() {
		
	}

	public boolean initialize(IFolder src, IFolder build) {
		
		// the project build-folder already holds our sources
		// because in our pipeline no source files but build-files are generated.
		// we see the the build-folder from featureIDE as source-folder.

		if (src != null) {
			this.source = src;
			this.sourceFolder = src.getRawLocation().toOSString();
		}
		
		if(build != null)
		{
			this.buildDirectory = build;
			this.buildFolder = build.getRawLocation().toOSString();				
		}
	
		return true;
	}

	private LinkedList<String> composeCMakeCommand(IFile config) {
		LinkedList<String> command = new LinkedList<String>();
				
		if (config != null) {	
			command.add(CMAKE_COMMAND);
			command.add(CMAKE_GENERATOR_OPT);
			command.add(CMAKE_GENERATOR);
			command.add(CMAKE_CACHE_OPT);
			command.add(config.getLocation().toFile().getAbsolutePath());
			command.add(sourceFolder);
		}
		
		return command;
	}
	
	/**
	 * @param file
	 */
	public void run(IFile file) {
		// TODO Auto-generated method stub
		
		assert (file != null && file.exists()) : CONFIGURATION_FILE_DOES_NOT_EXIST;
		try {
			if (!buildDirectory.exists())
				buildDirectory.create(false, true, null);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		
		LinkedList<String> command = composeCMakeCommand(file);
		
		String location=file.getLocation().removeLastSegments(1).toOSString();

		if(null != command)
		{
			process(command, location);
		}
	}
	

	private void process(AbstractList<String> command, String location) {
		// todo improvement run the process is an a eclipse console so that the user can see the output

		
		ProcessBuilder processBuilder = new ProcessBuilder(command);
		processBuilder.directory(new File(location));
		BufferedReader input = null;
		BufferedReader error = null;
		try {
			Process process = processBuilder.start();
			input = new BufferedReader(new InputStreamReader(
					process.getInputStream(), Charset.availableCharsets().get("UTF-8")));
			error = new BufferedReader(new InputStreamReader(
					process.getErrorStream(), Charset.availableCharsets().get("UTF-8")));
			while (true) {
				try {
					String line;
					while ((line = input.readLine()) != null) {								

							System.out.println(line);
					}
					while ((line = error.readLine()) != null)
						System.out.println(line);
						CMakeCorePlugin.getDefault().logWarning(line);
					try {
						process.waitFor();
					} catch (InterruptedException e) {
						CMakeCorePlugin.getDefault().logError(e);
					}
					int exitValue = process.exitValue();
					if (exitValue != 0) {
						throw new IOException(
								"The process doesn't finish normally (exit="
										+ exitValue + ")!");
					}
					break;
				} catch (IllegalThreadStateException e) {
					CMakeCorePlugin.getDefault().logError(e);
				}
			}
		} catch (IOException e) {
			CMakeCorePlugin.getDefault().logError(e);
		}finally{
			try {
				if(input!=null)input.close();
			} catch (IOException e) {
				CMakeCorePlugin.getDefault().logError(e);
			} finally {
				if(error!=null)
					try {
						error.close();
					} catch (IOException e) {
						CMakeCorePlugin.getDefault().logError(e);
					}
			}
		}
	}
	
	   private void findConsole(String name) {
//		      ConsolePlugin plugin = ConsolePlugin.getDefault();
//		      IConsoleManager conMan = plugin.getConsoleManager();
//
//		      IConsole cmakeConsole = CCorePlugin.getDefault().getBuildConsole("CMake Build console", "CMake Build console", null);
//		      
//		      cmakeConsole.start(project);
//		      
//		      org.eclipse.ui.console.IConsole[] existing = conMan.getConsoles();
//		      existing[0].getName();
		}
}
