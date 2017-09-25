/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.featurecpp.wrapper;

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
import java.net.URL;
import java.nio.charset.Charset;
import java.util.AbstractList;
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
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.MessageBox;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.internal.util.BundleUtility;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.featurecpp.FeatureCppCorePlugin;
import de.ovgu.featureide.fm.core.ModelMarkerHandler;

/**
 * Composes FeatureC++ files.
 *
 * @author Tom Brosch
 * @author Jens Meinicke
 */
@SuppressWarnings(RESTRICTION)
public class FeatureCppWrapper {

	private final static String EXE_LINUX_64BIT = "fc++v0.6Linux64bit";
	private final static String EXE_LINUX_32BIT = "fc++v0.8Linux32bit";
	private final static String EXE_MAC_OS_X = "fc++v0.8MacOSX";
	private final static String EXE_WINDOWS = "fc++v0.7WIN.exe";

	private ModelMarkerHandler<IResource> modelMarkerHandler;

	final String featureCppExecutableName;

	private String sourceFolder = null;

	private IFolder source = null;

	private String buildFolder = null;

	private IFolder buildDirectory = null;

	private int version = 7;

	public FeatureCppWrapper() {
		String featureCppExecutable;
		if (LINUX.equals(System.getProperty("os.name"))) {
			if (System.getProperty("os.arch").contains("64")) {
				featureCppExecutable = EXE_LINUX_64BIT;
				version = 6;
			} else {
				featureCppExecutable = EXE_LINUX_32BIT;
				// The current 32bit version does not support 0.7 commands
				version = 8;
			}
		} else if (System.getProperty("os.name").contains("Mac OS")) {
			featureCppExecutable = EXE_MAC_OS_X;
			version = 8;
		} else {
			featureCppExecutable = EXE_WINDOWS;
			version = 7;
		}
		URL url = BundleUtility.find(FeatureCppCorePlugin.getDefault().getBundle(), "lib/" + featureCppExecutable);
		try {
			url = FileLocator.toFileURL(url);
		} catch (final IOException e) {
			FeatureCppCorePlugin.getDefault().logError(e);
		}
		final Path path = new Path(url.getFile());
		final String pathName = path.toOSString();
		if (!path.isAbsolute()) {
			FeatureCppCorePlugin.getDefault().logWarning(pathName + IS_NOT_AN_ABSOLUTE_PATH_ + "fc++ can not be found.");
		}
		if (!path.isValidPath(pathName)) {
			FeatureCppCorePlugin.getDefault().logWarning(pathName + IS_NO_VALID_PATH_ + "fc++ can not be found.");
		}
		featureCppExecutableName = pathName;

		// The FeatureC++ needs to be executable
		new File(featureCppExecutableName).setExecutable(true);
	}

	public boolean initialize(IFolder source, IFolder build) {
		if (source != null) {
			this.source = source;
			sourceFolder = source.getRawLocation().toOSString();
		}
		buildFolder = build.getRawLocation().toOSString();
		buildDirectory = build;
		modelMarkerHandler = new ModelMarkerHandler<IResource>(build.getProject());
		return true;
	}

	public void compose(java.nio.file.Path config) {
		try {
			if (!buildDirectory.exists()) {
				buildDirectory.create(false, true, null);
			}
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		final LinkedList<String> command = new LinkedList<String>();
		command.add(featureCppExecutableName);
		if (version == 7) {
			command.add("--classinfo");
		}
		command.add("-o=" + buildFolder);
		command.add("-s=" + sourceFolder);
		if (version == 7) {
			command.add("--gpp");
		} else {
			command.add(GPP);
		}
		if (config != null) {
			command.add(config.toString());
			process(command);
		}
	}

	private void process(AbstractList<String> command) {
		final ProcessBuilder processBuilder = new ProcessBuilder(command);
		BufferedReader input = null;
		BufferedReader error = null;
		try {
			final Process process = processBuilder.start();
			input = new BufferedReader(new InputStreamReader(process.getInputStream(), Charset.availableCharsets().get("UTF-8")));
			error = new BufferedReader(new InputStreamReader(process.getErrorStream(), Charset.availableCharsets().get("UTF-8")));
			modelMarkerHandler.deleteAllModelMarkers();
			while (true) {
				try {
					String line;
					while ((line = input.readLine()) != null) {

						if (line.contains(" : warning: ")) {
							if (line.contains("warning: folder")) {
								modelMarkerHandler.createModelMarker(line, IMarker.SEVERITY_ERROR, 0);
							} else {
								addMarker(getFile(line), getMessage(line), getLineNumber(line));
							}
						}
						/** Lines to debug executing FeatureC++ **/
//						else {
//							FeatureCppCorePlugin.getDefault().logInfo("FeatureC++: " + line);
//						}
					}
					while ((line = error.readLine()) != null) {
						FeatureCppCorePlugin.getDefault().logWarning(line);
					}
					try {
						process.waitFor();
					} catch (final InterruptedException e) {
						FeatureCppCorePlugin.getDefault().logError(e);
					}
					final int exitValue = process.exitValue();
					if (exitValue != 0) {
						throw new IOException("The process doesn't finish normally (exit=" + exitValue + ")!");
					}
					break;
				} catch (final IllegalThreadStateException e) {
					FeatureCppCorePlugin.getDefault().logError(e);
				}
			}
		} catch (final IOException e) {
			openMessageBox(e);
			FeatureCppCorePlugin.getDefault().logError(e);
		} finally {
			try {
				if (input != null) {
					input.close();
				}
			} catch (final IOException e) {
				FeatureCppCorePlugin.getDefault().logError(e);
			} finally {
				if (error != null) {
					try {
						error.close();
					} catch (final IOException e) {
						FeatureCppCorePlugin.getDefault().logError(e);
					}
				}
			}
		}
	}

	/**
	 * Opens a message box if featureC++ could not be executed.
	 *
	 * @deprecated is set automatically at constructor.
	 */
	@Deprecated
	private void openMessageBox(IOException e) {
		if ((e != null) && (e.getCause() != null) && "java.io.IOException: java.io.IOException: error=13, Permission denied".equals(e.getCause().toString())) {
			final UIJob uiJob = new UIJob("") {

				@Override
				public IStatus runInUIThread(IProgressMonitor monitor) {
					final MessageBox d = new MessageBox(new Shell(), SWT.ICON_ERROR);
					d.setMessage("FeatureC++ can not be executed. Allow the file to be executed.\n" + SEE
						+ (LINUX.equals(System.getProperty("os.name")) ? "Properties/Permissions of " : "") + "file:\n" + "\t" + featureCppExecutableName);
					d.setText("FeatureC++ can not be executed.");
					d.open();
					return Status.OK_STATUS;
				}
			};
			uiJob.setPriority(Job.SHORT);
			uiJob.schedule();
		}
	}

	private IFile getFile(String line) {
		String fileName = line.substring(0, line.indexOf(" : warning:"));
		if (fileName.contains("(")) {
			fileName = fileName.substring(0, fileName.indexOf('('));
		}
		fileName = fileName.substring(sourceFolder.length() + 1);
		IFolder folder = source;
		while (!"".equals(fileName)) {
			if (!fileName.contains("\\")) {
				if (fileName.endsWith(".h")) {
					return folder.getFile(fileName);
				} else {
					return null;
				}
			} else {
				final String folderName = fileName.substring(0, fileName.indexOf('\\'));
				fileName = fileName.substring(fileName.indexOf('\\') + 1);
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
			line = line.substring(line.indexOf('(') + 1);
			return Integer.parseInt(line);
		}
		return 0;
	}

	private void addMarker(final IFile file, final String message, final int line) {
		final Job job = new Job(PROPAGATE_PROBLEM_MARKERS_FOR + CorePlugin.getFeatureProject(file)) {

			@Override
			public IStatus run(IProgressMonitor monitor) {
				try {
					if (!hasMarker(message, file)) {
						final IMarker newMarker = file.createMarker(CorePlugin.PLUGIN_ID + ".builderProblemMarker");
						newMarker.setAttribute(IMarker.MESSAGE, message);
						newMarker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
						newMarker.setAttribute(IMarker.LINE_NUMBER, line);
					}
				} catch (final CoreException e) {
					FeatureCppCorePlugin.getDefault().logError(e);
				}
				return Status.OK_STATUS;
			}

			private boolean hasMarker(String message, IFile sourceFile) {
				try {
					final IMarker[] marker = sourceFile.findMarkers(null, true, IResource.DEPTH_ZERO);
					if (marker.length > 0) {
						for (final IMarker m : marker) {
							if (message.equals(m.getAttribute(IMarker.MESSAGE, null))) {
								return true;
							}
						}
					}
				} catch (final CoreException e) {
					FeatureCppCorePlugin.getDefault().logError(e);
				}
				return false;
			}
		};
		job.setPriority(Job.DECORATE);
		job.schedule();
	}

}
