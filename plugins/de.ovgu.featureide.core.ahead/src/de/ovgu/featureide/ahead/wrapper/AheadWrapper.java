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
package de.ovgu.featureide.ahead.wrapper;

import jak2java.Jak2JavaWrapper;

import java.io.IOException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.ahead.AheadCorePlugin;
import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;


/**
 * The AheadWrapper class encapsulates all functionality that has to do
 * with the ahead tool suite. It provides methods to set the current
 * configuration file, to add jak files that should be recompiled due to an
 * incremental or full build. The build methods are capable of composing
 * jak files to java files as well as reduce jak files to java files and
 * compile java files to class files.
 * 
 * The actual work is than delegated to the dedicated wrapper classes.
 * 
 * @author Tom Brosch
 * @author Thomas Thuem
 */
public class AheadWrapper {

	private Jak2JavaWrapper jak2java;
	
	private ComposerWrapper composer;
	
	private static final String BUILDER_PROBLEM_MARKER = CorePlugin.PLUGIN_ID + ".builderProblemMarker";
	
	// Java 1.4 exclusions
	private static final String RAW_TYPE = "raw type";
	private static final String GENERIC_TYPE = "generic type";
	private static final String TYPE_SAFETY = "Type safety";
	private static final String TASK = "org.eclipse.jdt.core.task";
	
	public AheadWrapper(IFeatureProject featureProject) {
		jak2java = new Jak2JavaWrapper();
		composer = new ComposerWrapper(featureProject);
	}

	public void setConfiguration(IFile config) throws IOException {
		composer.setConfiguration(config);
	}

	public void addJakfile(IFile jakfile) {
		composer.addJakfileToCompose(jakfile);
	}

	public void buildAll() {
		IFile[] jakfiles = null;
		try {
			jakfiles = composer.composeAll();
		} catch (IOException ex) {
			CorePlugin.getDefault().logError(ex);
		}
		reduceJak2Java(jakfiles);
	}

	public void build() {
		reduceJak2Java(composer.compose());
	}
	
	public void setCompositionFolder(IFolder folder) {
		composer.setCompositionFolder(folder);
	}

	private IFile[] reduceJak2Java(IFile[] jakFiles) {
		
		IFile[] javaFiles = new IFile[jakFiles.length];
		String filename = null;
		for (int i = 0; i < jakFiles.length; i++) {
			IFile jakFile = jakFiles[i];
			if (jakFile.exists()) {
				jak2java.reduce2Java(jakFile.getRawLocation().toFile());

				filename = jakFile.getName();
				filename = filename.substring(0, filename.lastIndexOf('.'));
				javaFiles[i] = ((IFolder)jakFile.getParent()).getFile(filename
						+ ".java");
			}
		}
		return javaFiles;
	}
	
	public void addBuildErrorListener(AheadBuildErrorListener listener) {
		composer.addBuildErrorListener(listener);
	}

	public void postCompile(final IFile file) {
		final IFile jakFile = ((IFolder)file.getParent()).getFile(file.getName().replace(".java",".jak"));
		if (!jakFile.exists())
			return;
		
		// TODO #453 this job should not run parallel multiple times
		Job job = new Job("Propagate problem markers") {
			@Override
			public IStatus run(IProgressMonitor monitor) {
				try {
					if (file.exists() && jakFile.exists()) {
						IMarker[] markers = file.findMarkers(null, false, IResource.DEPTH_ZERO);
						if (markers != null) {
							for (IMarker marker : markers) {
								if (marker.exists() && !TASK.equals(marker.getType())) {
									String content = marker.getAttribute(IMarker.MESSAGE, null);
									if (content != null && (content.contains(RAW_TYPE) || content.contains(GENERIC_TYPE) || 
											content.contains(TYPE_SAFETY))) {
										marker.delete();
									} else {
										AheadBuildErrorEvent buildError = new AheadBuildErrorEvent(file, marker.getAttribute(IMarker.MESSAGE).toString(), AheadBuildErrorType.JAVAC_ERROR, (Integer)marker.getAttribute(IMarker.LINE_NUMBER));
										if (!hasMarker(buildError)) {
											IMarker newMarker = buildError.getResource().createMarker(BUILDER_PROBLEM_MARKER);
											if (newMarker.exists()) {
												newMarker.setAttribute(IMarker.LINE_NUMBER, buildError.getLine());
												newMarker.setAttribute(IMarker.MESSAGE, buildError.getMessage());
												newMarker.setAttribute(IMarker.SEVERITY, marker.getAttribute(IMarker.SEVERITY));
											}
										}
									}
								}
							}
						}
					}
				} catch (CoreException e) {
					/** avoid exception: Marker id xxx not found. **/
					if (!e.getMessage().startsWith("Marker")) {
						AheadCorePlugin.getDefault().logError(e);
					}
				}
				return Status.OK_STATUS;
			}

			private boolean hasMarker(AheadBuildErrorEvent buildError) {
				try {
					if (buildError.getResource().exists()) {
						int LineNumber = buildError.getLine();
						String Message = buildError.getMessage();
						IMarker[] marker = buildError.getResource().findMarkers(BUILDER_PROBLEM_MARKER, false, IResource.DEPTH_ZERO);
						if (marker.length > 0) {
							for (IMarker m : marker) {
								if (LineNumber == m.getAttribute(IMarker.LINE_NUMBER, -1)) {
									if (Message.equals(m.getAttribute(IMarker.MESSAGE, null))) {
										return true;
									}
								}
							}
						}
					}
				} catch (CoreException e) {
					AheadCorePlugin.getDefault().logError(e);
				}
				return false;
			}
		};
		job.setPriority(Job.DECORATE);
		job.schedule();
	}
}
