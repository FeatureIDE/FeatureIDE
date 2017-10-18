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
package de.ovgu.featureide.ahead.wrapper;

import static de.ovgu.featureide.fm.core.localization.StringTable.PROPAGATE_PROBLEM_MARKERS_FOR;

import java.io.IOException;
import java.util.Vector;

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
import jak2java.Jak2JavaWrapper;

/**
 * The AheadWrapper class encapsulates all functionality that has to do with the ahead tool suite. It provides methods to set the current configuration file, to
 * add jak files that should be recompiled due to an incremental or full build. The build methods are capable of composing jak files to java files as well as
 * reduce jak files to java files and compile java files to class files.
 *
 * The actual work is than delegated to the dedicated wrapper classes.
 *
 * @author Tom Brosch
 * @author Thomas Thuem
 */
public class AheadWrapper {

	private final Jak2JavaWrapper jak2java;

	private final ComposerWrapper composer;

	private Vector<IFile> files;

	private boolean createJob = true;

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
		} catch (final IOException ex) {
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

		final IFile[] javaFiles = new IFile[jakFiles.length];
		String filename = null;
		for (int i = 0; i < jakFiles.length; i++) {
			final IFile jakFile = jakFiles[i];
			if (jakFile.exists()) {
				jak2java.reduce2Java(jakFile.getRawLocation().toFile());

				filename = jakFile.getName();
				filename = filename.substring(0, filename.lastIndexOf('.'));
				javaFiles[i] = ((IFolder) jakFile.getParent()).getFile(filename + ".java");
			}
		}
		return javaFiles;
	}

	public void addBuildErrorListener(AheadBuildErrorListener listener) {
		composer.addBuildErrorListener(listener);
	}

	public void postCompile(IFile file) {
		final IFile jakFile = ((IFolder) file.getParent()).getFile(file.getName().replace(".java", ".jak"));
		if (!jakFile.exists()) {
			return;
		}

		if (files == null) {
			files = new Vector<IFile>();
		}
		if (!files.contains(file)) {
			files.add(file);
		}
		if (!createJob) {
			return;
		}
		createJob = false;
		final Job job =
			new Job((PROPAGATE_PROBLEM_MARKERS_FOR + CorePlugin.getFeatureProject(file)) != null ? CorePlugin.getFeatureProject(file).toString() : "") {

				@Override
				public IStatus run(IProgressMonitor monitor) {
					try {
						while (!files.isEmpty()) {
							final IFile file = files.remove(0);
							if (file.exists()) {
								final IMarker[] markers = file.findMarkers(null, false, IResource.DEPTH_ZERO);
								if (markers != null) {
									for (final IMarker marker : markers) {
										if (marker.exists() && !TASK.equals(marker.getType())) {
											final String content = marker.getAttribute(IMarker.MESSAGE, null);
											if ((content != null)
												&& (content.contains(RAW_TYPE) || content.contains(GENERIC_TYPE) || content.contains(TYPE_SAFETY))) {
												marker.delete();
											} else {
												final AheadBuildErrorEvent buildError =
													new AheadBuildErrorEvent(file, marker.getAttribute(IMarker.MESSAGE).toString(),
															AheadBuildErrorType.JAVAC_ERROR, (Integer) marker.getAttribute(IMarker.LINE_NUMBER));
												if (!hasMarker(buildError)) {
													final IResource res = buildError.getResource();
													if (res.exists()) {
														final IMarker newMarker = res.createMarker(BUILDER_PROBLEM_MARKER);
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
							}
						}
					} catch (final CoreException e) {
						/** avoid exception: Marker id xxx not found. **/
						if (!e.getMessage().startsWith("Marker")) {
							AheadCorePlugin.getDefault().logError(e);
						}
					} finally {
						createJob = true;
					}
					return Status.OK_STATUS;
				}

				private boolean hasMarker(AheadBuildErrorEvent buildError) {
					try {
						if (buildError.getResource().exists()) {
							final int LineNumber = buildError.getLine();
							final String Message = buildError.getMessage();
							final IMarker[] marker = buildError.getResource().findMarkers(BUILDER_PROBLEM_MARKER, false, IResource.DEPTH_ZERO);
							if (marker.length > 0) {
								for (final IMarker m : marker) {
									if (LineNumber == m.getAttribute(IMarker.LINE_NUMBER, -1)) {
										if (Message.equals(m.getAttribute(IMarker.MESSAGE, null))) {
											return true;
										}
									}
								}
							}
						}
					} catch (final CoreException e) {
						AheadCorePlugin.getDefault().logError(e);
					}
					return false;
				}
			};
		job.setPriority(Job.DECORATE);
		job.schedule();
	}
}
