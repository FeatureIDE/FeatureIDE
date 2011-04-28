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
package de.ovgu.featureide.featurecpp.wrapper;


import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.URL;
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.swt.widgets.MessageBox;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.internal.util.BundleUtility;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.featurecpp.FeatureCppCorePlugin;

/**
 * Composes FeatureC++ files.
 * 
 * @author Tom Brosch
 * @author Jens Meinicke
 */
@SuppressWarnings("restriction")
public class FeatureCppWrapper {

	final String featureCppExecutableName;

	private String sourceFolder = null;
	
	private IFolder source = null;

	private String buildFolder = null;

	private IFolder buildDirectory = null;
	
	private String featureCppExecutable = "fc++.exe";

	public FeatureCppWrapper() {
		String sys = System.getProperty("os.name");
        if (sys.equals("Linux")){
        	featureCppExecutableName = "fc++";
        	return;
        	// TODO use lib/fc++Linux
        	// featureCppExecutable = "fc++Linux";
        }
		URL url = BundleUtility.find(FeatureCppCorePlugin.getDefault().getBundle(), "lib/" + featureCppExecutable);
		try {
			url = FileLocator.toFileURL(url);
		} catch (IOException e) {
			FeatureCppCorePlugin.getDefault().logError(e);
		}
		Path path = new Path(url.getFile());
		String pathName = path.toOSString();
		if (!path.isAbsolute()) {
			FeatureCppCorePlugin.getDefault().logWarning(pathName + " is not an absolute path. " +
					"fc++.exe can not be found.");
		}
		if (!path.isValidPath(pathName)) {
			FeatureCppCorePlugin.getDefault().logWarning(pathName + " is no valid path. " +
					"fc++.exe can not be found.");
		}
		featureCppExecutableName = pathName;
	}

	public void initialize(IFolder source, IFolder build) {
		this.source = source;
		sourceFolder = source.getRawLocation().toOSString();
		buildFolder = build.getRawLocation().toOSString();
		buildDirectory = build;
	}

	public void compose(IFile config) {
		assert (config != null && config.exists()) : "Configuration file does not exist";
		IFolder folder2 = buildDirectory;
		try {
			if (!folder2.exists())
				folder2.create(false, true, null);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		LinkedList<String> command = new LinkedList<String>();
		command.add(featureCppExecutableName);
		command.add("--classinfo");
		command.add("-o=" + buildFolder);
		command.add("-s=" + sourceFolder);
		command.add("--gpp");
		command.add(config.getRawLocation().toOSString());
		process(command);

	}

	private void process(LinkedList<String> command) {
		ProcessBuilder processBuilder = new ProcessBuilder(command);
		BufferedReader input = null;
		BufferedReader error = null;
		try {
			Process process = processBuilder.start();
			 input = new BufferedReader(new InputStreamReader(
					process.getInputStream()));
			 error = new BufferedReader(new InputStreamReader(
					process.getErrorStream()));
			boolean x = true;
			while (x) {
				try {
					String line;
					while ((line = input.readLine()) != null) {
						if (line.contains(" : warning: ")) {
							addMarker(getFile(line), getMessage(line), getLineNumber(line));
						}
						else
							FeatureCppCorePlugin.getDefault().logInfo("FeatureC++: " + line);
					}
					while ((line = error.readLine()) != null)
						FeatureCppCorePlugin.getDefault().logWarning(line);
					int exitValue = process.exitValue();
					if (exitValue != 0) {
						throw new IOException(
								"The process doesn't finish normally (exit="
										+ exitValue + ")!");
					}
					x = false;
				} catch (IllegalThreadStateException e) {
					FeatureCppCorePlugin.getDefault().logError(e);
				}
			}
		} catch (IOException e) {
			String os = System.getProperty("os.name");
			if (os.equals("Linux")) {
				if (e.getLocalizedMessage().equals(
						"Cannot run program \"fc++\": java.io.IOException: error=2, No such file or directory")) {
					UIJob uiJob = new UIJob("") {
						public IStatus runInUIThread(IProgressMonitor monitor) {
							Shell parentShell = new Shell();
							MessageBox d =  new MessageBox(parentShell);
							d.setMessage("fc++ could not be found. Please install fc++.\n" +
									"See:\n" +
									"    http://wwwiti.cs.uni-magdeburg.de/iti_db/fcc/.");
							d.setText("fc++ not found");
							d.open();
							return Status.OK_STATUS;
						}
					};
					uiJob.setPriority(Job.SHORT);
					uiJob.schedule();
				}
			}
			FeatureCppCorePlugin.getDefault().logError(e);
		}finally{
			try {
				if(input!=null)input.close();
				if(error!=null)error.close();
			} catch (IOException e) {
				FeatureCppCorePlugin.getDefault().logError(e);
			}
		}
	}

	private IFile getFile(String line) {
		String fileName = line.substring(0, line.indexOf(" : warning:"));
		if (fileName.contains("(")) {
			fileName = fileName.substring(0,fileName.indexOf("("));
		}
		fileName = fileName.substring(sourceFolder.length() +1);
		IFolder folder = source;
		while (fileName != "") {
			if (!fileName.contains("\\")) {
				if (fileName.endsWith(".h")) {
					return folder.getFile(fileName);
				} else {
					return null;
				}
			} else {
				String folderName = fileName.substring(0, fileName.indexOf("\\"));
				fileName = fileName.substring(fileName.indexOf("\\") + 1);
				folder = folder.getFolder(folderName);
			}
		}
		return null;
	}
	
	private String getMessage(String line) {
		return line.substring(line.indexOf(" : warning: ") + 12);
	}

	private int getLineNumber(String line) {
		if (line.contains(") : warning: ")) {
			line = line.substring(0, line.indexOf(") : warning: "));
			line = line.substring(line.indexOf("(") + 1);
			return Integer.parseInt(line);
		}
		return 0;
	}

	private void addMarker(final IFile file, final String message, final int line) {
		Job job = new Job("Propagate problem markers") {
			@Override
			public IStatus run(IProgressMonitor monitor) {
				try {
					if (!hasMarker(message, file)) {
						IMarker newMarker = file.createMarker(CorePlugin.PLUGIN_ID + ".builderProblemMarker");
						newMarker.setAttribute(IMarker.MESSAGE, message);
						newMarker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
						newMarker.setAttribute(IMarker.LINE_NUMBER, line);
					}
				} catch (CoreException e) {
					FeatureCppCorePlugin.getDefault().logError(e);
				}
				return Status.OK_STATUS;
			}
			
			private boolean hasMarker(String message, IFile sourceFile) {
				try {
					IMarker[] marker = sourceFile.findMarkers(null, true, IResource.DEPTH_ZERO);
					if (marker.length > 0) {
						for (IMarker m : marker) {
							if (message.equals(m.getAttribute(IMarker.MESSAGE, null))) {
								return true;
							}
						}
					}
				} catch (CoreException e) {
					FeatureCppCorePlugin.getDefault().logError(e);
				}
				return false;
			}
		};
		job.setPriority(Job.DECORATE);
		job.schedule();
	}

}
