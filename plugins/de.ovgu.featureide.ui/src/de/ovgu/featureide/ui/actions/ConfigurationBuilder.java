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
package de.ovgu.featureide.ui.actions;

import java.io.CharArrayWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.AbstractList;
import java.util.LinkedList;
import java.util.Scanner;
import java.util.TreeMap;
import java.util.regex.Matcher;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.core.JavaProject;

import com.sun.tools.javac.Main;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationReader;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * Builds all valid or current configurations for a selected feature project.
 * 
 * @author Jens Meinicke
 */
@SuppressWarnings("restriction")
public class ConfigurationBuilder implements IConfigurationBuilderBasics {
	private IFeatureProject project;
	private IFolder folder;
	private FeatureModel featureModel;
	private Configuration configuration;
	private ConfigurationReader reader;
	private long confs;
	private String zeros;
	private int configurationNumber = 0;
	private boolean counting = true;
	private String classpath = "";
	private IFolder tmp;
	private boolean compile;
	
	/**
	 * Starts the build process for valid or current configurations for the given feature project.
	 * @param featureProject The feature project
	 * @param buildAllValidConfigurations <code>true</code> if all possible valid configurations should be build<br>
	 * <code>false</code> if all current configurations should be build
	 * @param compile <code>true</code> if the compiler should be performed after build.
	 * @see BuildAllConfigurationsAction
	 * @see BuildAllValidConfigurationsAction
	 */
	ConfigurationBuilder(final IFeatureProject featureProject, final boolean buildAllValidConfigurations, boolean compile) {
		project = featureProject;
		featureModel = project.getFeatureModel();
		this.compile = compile;
		if (!buildAllValidConfigurations) {
			configurationNumber = countConfigurations(featureProject.getConfigFolder());
		} else {
			Job number = new Job(JOB_TITLE_COUNT_CONFIGURATIONS) {
				public IStatus run(IProgressMonitor monitor) {
					configurationNumber = (int)new Configuration(featureModel, false, false).number(1000000);
					return Status.OK_STATUS;
				}
			};
			number.setPriority(Job.LONG);
			number.schedule();
		}
			
		Job job = new Job(buildAllValidConfigurations ? JOB_TITLE : JOB_TITLE_CURRENT) {
			public IStatus run(IProgressMonitor monitor) {
				try {
					long time = System.currentTimeMillis();
					monitor.beginTask("" , 1);
					
					init(monitor, buildAllValidConfigurations);
					
					monitor.setTaskName(SUBTASK_GET + confs + "/" + (configurationNumber == 0 ? "counting..." : configurationNumber));
					if (buildAllValidConfigurations) {
						buildAll(featureModel.getRoot(), monitor);
					} else {
						buildActivConfigurations(featureProject, monitor);
					}
					try {
						folder.refreshLocal(IResource.DEPTH_INFINITE, null);
					} catch (CoreException e) {
						UIPlugin.getDefault().logError(e);
					}
					
					time = System.currentTimeMillis() - time;
					long s = (time/1000)%60;
					long min = (time/(60 * 1000))%60;
					long h = time/(60 * 60 * 1000);
					String t = h + "h " + (min < 10 ? "0" + min : min) + "min " + (s < 10 ? "0" + s : s) + "s.";
					UIPlugin.getDefault().logInfo(confs-1 + (configurationNumber != 0 ? " of " + configurationNumber : "") + " configurations built in " + t);
				} finally {
					monitor.done();
				}
				return Status.OK_STATUS;
			}

			
			
		};
		job.setPriority(Job.LONG);
		job.schedule();
	}
	
	/**
	 * Initializes the configuration builder.<br>
	 * -Removes old products
	 * -Generates the build folder
	 * @param monitor
	 * @param buildAllValidConfigurations<code>true</code> if all possible valid configurations should be build<br>
	 * <code>false</code> if all current configurations should be build
	 */
	private void init(IProgressMonitor monitor, boolean buildAllValidConfigurations) {
		confs = 1;
		folder = project.getProject().getFolder(buildAllValidConfigurations ? FOLDER_NAME : FOLDER_NAME_CURRENT);
		if (!folder.exists()) {
			try {
				folder.create(true, true, null);
			} catch (CoreException e) {
				UIPlugin.getDefault().logError(e);
			}
		} else {
			try {
				int countProducts = folder.members().length;
				int current = 1;
				for (IResource res : folder.members()) {
					monitor.setTaskName("Remove old products : " + current + "/" + countProducts);
					current++;
					res.delete(true, null);
				}
			} catch (CoreException e) {
				UIPlugin.getDefault().logError(e);
			}
		}
		configuration = new Configuration(featureModel);
		reader = new ConfigurationReader(configuration);
		project.getComposer().initialize(project);
		
		if (compile) {
			setClassPath();
		
			tmp = folder.getFolder(TEMPORARY_BIN_FOLDER);
			if (!tmp.exists()) {
				try {
					tmp.create(true, true, null);
				} catch (CoreException e) {
					UIPlugin.getDefault().logError(e);
				}
			}
		}
	}
	
	/**
	 * Sets the java classPath for compiling.
	 */
	private void setClassPath() {
		String sep = System.getProperty("path.separator");
		try {
			JavaProject proj = new JavaProject(project.getProject(), null);
			IJavaElement[] elements = proj.getChildren();
			for (IJavaElement e : elements) {
				String path = e.getPath().toOSString();
				if (path.contains(":")) {
					classpath += sep + path;
					continue;
				}
				IResource resource = e.getResource();
				if (resource != null && "jar".equals(resource.getFileExtension())) {
					classpath += sep + resource.getRawLocation().toOSString();
				}
			}
		} catch (JavaModelException e) {
			
		}			
		classpath = classpath.length() > 0 ? classpath.substring(1) : classpath;
	}
	
	/**
	 * Compiles the built configuration to create error markers.
	 * The binary files will be placed into an temporary folder.
	 * @param confName
	 */
	private void compile(String confName) {	
		LinkedList<IFile> files = getJavaFiles(folder.getFolder(confName));
		LinkedList<String> options = new LinkedList<String>();
		options.add("-g");
		options.add("-Xlint");
		options.add("-d");
		options.add(tmp.getRawLocation().toOSString());
		options.add("-classpath");
		options.add(classpath);
		for (IFile file : files) {
			options.add(file.getRawLocation().toOSString());
		}
		
		CharArrayWriter charWriter = new CharArrayWriter();
		Main.compile(toArray(options), new PrintWriter(charWriter));
		files = parseJavacOutput(charWriter.toString(), files, confName);
		for (IFile file : files) {
			project.getComposer().postCompile(null, file);
		}
	}

	/**
	 * Converts a given <code>LinkedList</code> into an <code>array</code>.
	 * @param list a LinkedList
	 * @return the corresponding array
	 */
	private String[] toArray(AbstractList<String> list) {
		String[] array = new String[list.size()];
		for(int i = 0;i < list.size();i++) {
			array[i] = list.get(i);
		}
		return array;
	}

	/**
	 * Generates the problem markers from the given compiler output. 
	 * @param output The output from the compiler
	 * @param files The compiled files
	 * @param configurationName Name of the actual configuration
	 * @return 
	 */
	public LinkedList<IFile> parseJavacOutput(String output, LinkedList<IFile> files, String configurationName) {
		LinkedList<IFile> errorFiles = new LinkedList<IFile>();
		if (output.length() == 0)
			return errorFiles;
		TreeMap<String, IFile> sourcePaths = new TreeMap<String, IFile>();
		for (IFile file : files)
			sourcePaths.put(file.getRawLocation().toOSString(), file);

		Scanner scanner = new Scanner(output);
		String currentLine;
		while (scanner.hasNextLine()) {
			currentLine = scanner.nextLine();

			Matcher matcher = errorMessagePattern.matcher(currentLine);
			if (!matcher.find() || !sourcePaths.containsKey(matcher.group(1)))
				continue;
			IFile currentFile = sourcePaths.get(matcher.group(1));
			int line = Integer.parseInt(matcher.group(2));

			String errorMessage = matcher.group(3);
			errorMessage = errorMessage.substring(1);

			if (CANNOT_FIND_SYMBOL.equals(errorMessage)) {
				errorMessage = parseCannotFindSymbolMessage(scanner);
			}
			if (errorMessage.contains(ERROR_IGNOR_RAW_TYPE) || errorMessage.contains(ERROR_IGNOR_CAST) 
					|| errorMessage.contains(ERROR_IGNOR_SERIIZABLE) 
					|| errorMessage.contains(ERROR_IGNOR_DEPRECATION)) {
				continue;
			}
			if (!errorFiles.contains(currentFile)) {
				errorFiles.add(currentFile);
			}
			IMarker newMarker;
			try {
				newMarker = currentFile.createMarker(PROBLEM_MARKER);
				if (newMarker.exists()) {
					newMarker.setAttribute(IMarker.LINE_NUMBER, line);
					newMarker.setAttribute(IMarker.MESSAGE, configurationName + " " + errorMessage);
					newMarker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
				}
			} catch (CoreException e) {
				UIPlugin.getDefault().logError(e);
			}
		}
		return errorFiles;
	}

	private String parseCannotFindSymbolMessage(Scanner scanner) {
		while (scanner.hasNextLine()) {
			String currentLine = scanner.nextLine();
			if (currentLine.startsWith("symbol")) {
				String[] tokens = currentLine.split(": ");
				if (tokens.length == 2)
					return CANNOT_FIND_SYMBOL + ": "+ tokens[1];
				break;
			}
		}
		return CANNOT_FIND_SYMBOL;
	}

	/**
	 * Looks for all java files at the given folder.
	 * @param folder The folder containing the java files
	 * @return A list with all java files at the folder
	 */
	private LinkedList<IFile> getJavaFiles(IFolder folder) {
		LinkedList<IFile> files = new LinkedList<IFile>();
		try {
			for (IResource res : folder.members()) {
				if (res instanceof IFolder) {
					files.addAll(getJavaFiles((IFolder)res));
				} else if ("java".equals(res.getFileExtension())) {
					files.add((IFile)res);
				}
			}
		} catch (CoreException e) {
			UIPlugin.getDefault().logError(e);
		}
		return files;
	}

	/**
	 * Builds all current configurations for the given feature project into the folder for current configurations.
	 * @param featureProject The feature project
	 * @param monitor 
	 */
	protected void buildActivConfigurations(IFeatureProject featureProject, IProgressMonitor monitor) {
		monitor.beginTask("" , configurationNumber);
		try {
			for (IResource configuration : featureProject.getConfigFolder().members()) {
				if (monitor.isCanceled()) {
					return;
				}
				if (isConfiguration(configuration)) {
					build(configuration, monitor);
				}
			}
		} catch (CoreException e) {
			UIPlugin.getDefault().logError(e);
		}
	}


	/**
	 * Builds the given configuration file into the folder for current configurations.
	 * @param configuration The configuration file
	 * @param monitor 
	 */
	private void build(IResource configuration, IProgressMonitor monitor) {
		try {
			reader.readFromFile((IFile)configuration);
			monitor.setTaskName(SUBTASK_BUILD + confs + "/" + configurationNumber);
			project.getComposer().buildConfiguration(folder.getFolder(configuration.getName().split("[.]")[0]), this.configuration);
			if (monitor.isCanceled()) {
				return;
			}
			confs++;
			folder.getFolder(configuration.getName().split("[.]")[0]).refreshLocal(IResource.DEPTH_INFINITE, null);
			if (compile) {
				monitor.setTaskName(SUBTASK_COMPILE + confs + "/" + configurationNumber);
				compile(configuration.getName().split("[.]")[0]);
			}
			if (confs <= configurationNumber) { 
				monitor.setTaskName(SUBTASK_GET + confs + "/" + configurationNumber);
			}
			monitor.worked(1);
		} catch (CoreException e) {
			UIPlugin.getDefault().logError(e);
		} catch (IOException e) {
			UIPlugin.getDefault().logError(e);
		}
	}

	/**
	 * Counts the configurations at the given folder.
	 * @param configFolder The folder
	 * @return Number of configuration files
	 */
	private int countConfigurations(IFolder configFolder) {
		int i = 0;
		try {
			for (IResource res : configFolder.members()) {
				if (isConfiguration(res)) {
					i++;
				}		
			}
		} catch (CoreException e) {
			UIPlugin.getDefault().logError(e);
		}
		return i;
	}

	/**
	 * @param res A file.
	 * @return <code>true</code> if the given file is a configuration file
	 */
	private boolean isConfiguration(IResource res) {
		return res instanceof IFile && CorePlugin.getDefault().getConfigurationExtensions().contains("." + res.getFileExtension());
	}
	
	/**
	 * Builds all possible valid configurations for the feature project.<br>
	 * Iterates through the structure of the feature model and ignores constraints, to get a linear expenditure.<br>
	 * After collecting a configurations the satsolver tests its validity.<br>
	 * Then the found configuration will be build into the folder for all valid products.
	 * @param root The root feature of the feature model
	 * @param monitor
	 */
	private void buildAll(Feature root, IProgressMonitor monitor) {
		LinkedList<Feature> selectedFeatures2 = new LinkedList<Feature>();
		selectedFeatures2.add(root);
		build(root, "", selectedFeatures2, monitor);
	}

	private void build(Feature currentFeature, String selected, LinkedList<Feature> selectedFeatures2, IProgressMonitor monitor) {
		if (monitor.isCanceled() || (configurationNumber != 0 && confs > configurationNumber)) {
			return;
		}
		if (selectedFeatures2.isEmpty()) {
			if (reader.readFromString(selected)) {
				if (configuration.valid()) {
					LinkedList<String> selectedFeatures3 = new LinkedList<String>();
					for (String f : selected.split("[ ]")) {
						if (!"".equals(f)) {
							selectedFeatures3.add(f);
						}
					}
					for (Feature f : configuration.getSelectedFeatures()) {
						if (f.isLayer()) {
							if (!selectedFeatures3.contains(f.getName())) {
								return;
							}
						}
					}
					for (String f : selectedFeatures3) {
						if (configuration.getSelectablefeature(f).getSelection() != Selection.SELECTED) {
							return;
						}
					}
					
					if (confs < 10) {
						zeros = "000";
					} else if (confs < 100) {
						zeros = "00";
					} else if (confs < 1000) {
						zeros = "0";
					} else {
						zeros = "";
					}
					monitor.setTaskName(SUBTASK_BUILD + confs + "/" + (configurationNumber == 0 ? "counting..." : configurationNumber));
					project.getComposer().buildConfiguration(folder.getFolder(CONFIGURATION_NAME + zeros + confs), configuration);
					try {
						folder.getFolder(CONFIGURATION_NAME + zeros + confs).refreshLocal(IResource.DEPTH_INFINITE, null);
					} catch (CoreException e) {
						UIPlugin.getDefault().logError(e);
					}
					
					if (compile) {
						monitor.setTaskName(SUBTASK_COMPILE + confs + "/" + configurationNumber);
						compile(CONFIGURATION_NAME + zeros + confs);
					}
					
					confs++;
					if (confs <= configurationNumber || configurationNumber == 0) { 
						monitor.setTaskName(SUBTASK_GET + confs + "/" + (configurationNumber == 0 ? "counting..." : configurationNumber));
					}
					if (counting && configurationNumber != 0) {
						counting = false;
						monitor.beginTask("" , configurationNumber);
						monitor.worked((int)confs);
					}
					if (configurationNumber != 0) {
						monitor.worked(1);
					}
				}
			}
			return;
		}
		
		if (currentFeature.isAnd()) {
			buildAnd(selected, selectedFeatures2, monitor);
		} else if (currentFeature.isOr()) {
			buildOr(selected, selectedFeatures2, monitor);
		} else if (currentFeature.isAlternative()) {
			buildAlternative(selected, selectedFeatures2, monitor);
		}				
	}

	private void buildAlternative(String selected, LinkedList<Feature> selectedFeatures2, IProgressMonitor monitor) {
		Feature currentFeature = selectedFeatures2.getFirst();
		selectedFeatures2.removeFirst();
		LinkedList<Feature> selectedFeatures3 = new LinkedList<Feature>();
		if (currentFeature.isLayer()) {
			if ("".equals(selected)) {
				selected = currentFeature.getName();
			} else {
				selected += " " + currentFeature.getName();
			}
		}
		if (!currentFeature.hasChildren()) {
			if (selectedFeatures2.isEmpty()) {
				currentFeature = null;
			} else {
				currentFeature = selectedFeatures2.getFirst();
			}
			selectedFeatures3.addAll(selectedFeatures2);
			build(currentFeature, selected, selectedFeatures3, monitor);
			return;
		}
		for (int i2 = 0;i2 < getChildren(currentFeature).size();i2++) {
			selectedFeatures3 = new LinkedList<Feature>();
			selectedFeatures3.add(getChildren(currentFeature).get(i2));
			selectedFeatures3.addAll(selectedFeatures2);
			build(selectedFeatures3.isEmpty() ? null : selectedFeatures3.getFirst(), selected, selectedFeatures3, monitor);
		}
	}


	private void buildOr(String selected, LinkedList<Feature> selectedFeatures2, IProgressMonitor monitor) {
		Feature currentFeature = selectedFeatures2.getFirst();
		selectedFeatures2.removeFirst();
		LinkedList<Feature> selectedFeatures3 = new LinkedList<Feature>();
		if (currentFeature.isLayer()) {
			if ("".equals(selected)) {
				selected = currentFeature.getName();
			} else {
				selected += " " + currentFeature.getName();
			}
		}
		if (!currentFeature.hasChildren()) {
			if (selectedFeatures2.isEmpty()) {
				currentFeature = null;
			} else {
				currentFeature = selectedFeatures2.getFirst();
			}
			selectedFeatures3.addAll(selectedFeatures2);
			build(currentFeature, selected, selectedFeatures3, monitor);
			return;
		}
		int k2;
		int i2 = 1;
		if (getChildren(currentFeature).size() < currentFeature.getChildren().size()) {
			i2 = 0;
		}
		for (;i2 < (int)java.lang.Math.pow(2, getChildren(currentFeature).size());i2++) {
			k2 = i2;
			selectedFeatures3 = new LinkedList<Feature>();
			for (int j = 0;j < getChildren(currentFeature).size();j++) {
				if (k2%2 != 0) {
					selectedFeatures3.add(getChildren(currentFeature).get(j));
				}
				k2 = k2/2;
			}
			selectedFeatures3.addAll(selectedFeatures2);
			build(selectedFeatures3.isEmpty() ? null : selectedFeatures3.getFirst(), selected, selectedFeatures3, monitor);
		}
	}

	private void buildAnd(String selected, LinkedList<Feature> selectedFeatures2, IProgressMonitor monitor) {
		Feature currentFeature = selectedFeatures2.getFirst();
		selectedFeatures2.removeFirst();
		LinkedList<Feature> selectedFeatures3 = new LinkedList<Feature>();
		if (currentFeature.isLayer()) {
			if ("".equals(selected)) {
				selected = currentFeature.getName();
			} else {
				selected += " " + currentFeature.getName();
			}
		}
		if (!currentFeature.hasChildren()) {
			if (selectedFeatures2.isEmpty()) {
				currentFeature = null;
			} else {
				currentFeature = selectedFeatures2.getFirst();
			}
			selectedFeatures3.addAll(selectedFeatures2);
			build(currentFeature, selected, selectedFeatures3, monitor);
			return;
		}
		int k2;
		LinkedList<Feature> optionalFeatures = new LinkedList<Feature>();
		for (Feature f : getChildren(currentFeature)) {
			if (f.isMandatory()) {
				selectedFeatures2.add(f);
			} else {
				optionalFeatures.add(f);
			}
		}
		for (int i2 = 0;i2 < (int)java.lang.Math.pow(2, optionalFeatures.size());i2++) {
			k2 = i2;
			selectedFeatures3 = new LinkedList<Feature>();
			for (int j = 0;j < optionalFeatures.size();j++) {
				if (k2%2 != 0) {
					selectedFeatures3.add(optionalFeatures.get(j));
				}
				k2 = k2/2;
			}
			selectedFeatures3.addAll(selectedFeatures2);
			build(selectedFeatures3.isEmpty() ? null : selectedFeatures3.getFirst(), selected, selectedFeatures3, monitor);
		}
		
	}

	/**
	 * Returns all children of a feature if it is a layer or if it has a child that is a layer.
	 * @param currentFeature The feature
	 * @return The children
	 */
	private LinkedList<Feature> getChildren(Feature currentFeature) {
		LinkedList<Feature> children = new LinkedList<Feature>();
		for (Feature child : currentFeature.getChildren()) {
			if (child.isLayer() || hasLayerChild(child)) {
				children.add(child);
			}
		}
		return children;
	}

	/**
	 * @param feature The feature
	 * @return <code>true</code> if  the feature is a layer or if it has a child that is a layer
	 */
	private boolean hasLayerChild(Feature feature) {
		if (feature.hasChildren()) {
			for (Feature child : feature.getChildren()) {
				if (child.isLayer() || hasLayerChild(child)) {
					return true;
				}
			}
		}
		return false;
	}
}
