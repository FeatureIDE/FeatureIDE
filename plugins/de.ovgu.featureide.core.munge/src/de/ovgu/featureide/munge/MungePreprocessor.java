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
package de.ovgu.featureide.munge;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.Scanner;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.sonatype.plugins.munge.Munge;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.munge.model.MungeModelBuilder;

/**
 * Munge: a purposely-simple Java preprocessor.
 * 
 * @author Jens Meinicke
 */
public class MungePreprocessor extends ComposerExtensionClass{
	
	private LinkedList<String> selectedFeatures;
	
	private ArrayList<String> features;
	
	private MungeModelBuilder mungeModelBuilder;

	@Override
	public void initialize(IFeatureProject project) {
		super.initialize(project);
		mungeModelBuilder = new MungeModelBuilder(project);
	}
	
	@Override
	public ArrayList<String> extensions() {
		ArrayList<String> extensions = new ArrayList<String>();
		extensions.add(".java");
		return extensions;
	}

	public void performFullBuild(IFile config) {
		assert(featureProject != null) : "Invalid project given";
		
		final String configPath =  config.getRawLocation().toOSString();
		final String basePath = featureProject.getSourcePath();
		final String outputPath = featureProject.getBuildPath();
		
		if (configPath == null || basePath == null || outputPath == null)
			return;
		
		//CommandLine syntax:
		//	–DFEATURE1 –DFEATURE2 ... File1.java File2.java ... outputDirectory
		
		// add symbol definitions
		features = readFeaturesfromConfigurationFile(config.getRawLocation().toFile()); 
		if (features == null) {
			return;
		}
		selectedFeatures = new LinkedList<String>();
		for (String feature : features) {
			selectedFeatures.add(feature);
		}
		
		//add source files
		try {
			addDefaultSourceFiles(featureProject.getSourceFolder());
		} catch (CoreException e) {
			MungeCorePlugin.getDefault().logError(e);
		}
		
		mungeModelBuilder.buildModel();
	}
	
	public ArrayList<String> readFeaturesfromConfigurationFile(File file) {
		Scanner scanner = null;
		try {
			ArrayList<String> list;
			scanner = new Scanner(file);
			if (scanner.hasNext()) {
				list = new ArrayList<String>();
				while (scanner.hasNext()) {
					list.add(scanner.next());
				}
				return list;
			} else {
				return null;
			}
		} catch (FileNotFoundException e) {
			MungeCorePlugin.getDefault().logError(e);
		} finally {
			if (scanner != null) {
				scanner.close();
			}
		}
		return null;
	}

	private void addDefaultSourceFiles(IFolder sourceFolder) throws CoreException {
		ArrayList<String> args = new ArrayList<String>();
		for (String feature : features) {
			args.add("-D" + feature);
		}
		
		boolean filesAdded = false;
		for (IResource res : sourceFolder.members()) {
			if (res instanceof IFolder) {
				addSourceFiles((IFolder)res, featureProject.getBuildFolder().getFolder(res.getName()));
			} else if (res instanceof IFile){
				args.add(res.getRawLocation().toOSString());
				filesAdded = true;
			}
		}

		if (!filesAdded)
			return;
		
		//add output directory
		args.add(featureProject.getBuildFolder().getRawLocation().toOSString());
		runMunge(args);
	}

	private void addSourceFiles(IFolder sourceFolder, IFolder buildFolder) throws CoreException {
		ArrayList<String> args = new ArrayList<String>();
		for (String feature : features) {
			args.add("-D" + feature);
		}
		createBuildFolder(buildFolder);
		boolean filesAdded = false;
		for (IResource res : sourceFolder.members()) {
			if (res instanceof IFolder) {
				addSourceFiles((IFolder)res, buildFolder.getFolder(res.getName()));
			} else 
			if (res instanceof IFile){
				if (res.getName().endsWith(".java")) {
					args.add(res.getRawLocation().toOSString());
					filesAdded = true;
				}
			}
		}

		if (!filesAdded)
			return;
		
		//add output directory
		args.add(buildFolder.getRawLocation().toOSString());
		runMunge(args);
	}
	
	private void runMunge(ArrayList<String> args) {
		//convert into an Array
		String[] argArray = new String[args.size()];
		for (int i = 0;i < args.size();i++) {
			argArray[i] = args.get(i);
			System.out.println(args.get(i));
		}
		//run Munge
		Munge m = new Munge();
		m.main(argArray, featureProject);
	}

	private void createBuildFolder(IFolder buildFolder) throws CoreException {
		if (!buildFolder.exists()) {
			buildFolder.create(true, true, null);
		}
		buildFolder.refreshLocal(IResource.DEPTH_ZERO, null);
	}

	@Override
	public ArrayList<String[]> getTemplates() {
		ArrayList<String[]> list = new ArrayList<String[]>();
		String[] java = {"Java", "java", "public class #classname# {\n\n}"};
		list.add(java);
		return list;
	}

	@Override
	public void postCompile(IResourceDelta delta, final IFile file) {
		super.postCompile(delta, file);
		Job job = new Job("Propagate problem markers") {
			@Override
			public IStatus run(IProgressMonitor monitor) {
				try {
					IMarker[] marker = file.findMarkers(null, false, IResource.DEPTH_ZERO);
					if (marker.length != 0) {
						for (IMarker m : marker) {
							IFile sourceFile = findSourceFile(file, featureProject.getSourceFolder());
							if (!hasMarker(m, sourceFile)) {
								IMarker newMarker = sourceFile.createMarker(CorePlugin.PLUGIN_ID + ".builderProblemMarker");
								newMarker.setAttribute(IMarker.LINE_NUMBER, m.getAttribute(IMarker.LINE_NUMBER));
								newMarker.setAttribute(IMarker.MESSAGE, m.getAttribute(IMarker.MESSAGE));
								newMarker.setAttribute(IMarker.SEVERITY, m.getAttribute(IMarker.SEVERITY));
							}
						}
					}
				} catch (CoreException e) {
					MungeCorePlugin.getDefault().logError(e);
				}
				return Status.OK_STATUS;
			}
			
			private boolean hasMarker(IMarker buildMarker, IFile sourceFile) {
				try {
					IMarker[] marker = sourceFile.findMarkers(null, true, IResource.DEPTH_ZERO);
					int LineNumber = buildMarker.getAttribute(IMarker.LINE_NUMBER, -1);
					String Message = buildMarker.getAttribute(IMarker.MESSAGE, null);
					if (marker.length > 0) {
						for (IMarker m : marker) {
							if (LineNumber == m.getAttribute(IMarker.LINE_NUMBER, -1)) {
								if (Message.equals(m.getAttribute(IMarker.MESSAGE, null))) {
									return true;
								}
							}
						}
					}
				} catch (CoreException e) {
					MungeCorePlugin.getDefault().logError(e);
				}
				return false;
			}
		};
		job.setPriority(Job.DECORATE);
		job.schedule();
	}
	
	private IFile findSourceFile(IFile file, IFolder folder) throws CoreException {
		for (IResource res: folder.members()) {
			if (res instanceof IFolder) {
				IFile sourceFile = findSourceFile(file, (IFolder)res);
				if (sourceFile != null) {
					return sourceFile;
				}
			} else if (res instanceof IFile) {
				if (res.getName().equals(file.getName()))
					return (IFile)res;
			}
		}
		return null;
	}

	@Override
	public boolean hasFeatureFolders() {
		return false;
	}
	
	@Override
	public void buildFSTModel() {
		mungeModelBuilder.buildModel();
	}
}
