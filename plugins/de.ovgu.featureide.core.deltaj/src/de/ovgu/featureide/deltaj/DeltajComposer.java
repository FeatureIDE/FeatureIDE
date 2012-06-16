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
package de.ovgu.featureide.deltaj;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.xtext.example.util.DJIdeProperties;
import org.xtext.example.util.ValidationStatus;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationReader;
import djtemplates.DJStandaloneCompiler;

/**
 * DeltaJ Composer
 * 
 * @author Fabian Benduhn
 */
public class DeltajComposer extends ComposerExtensionClass {
	public static final String JAVA_NATURE = "org.eclipse.jdt.core.javanature";
	private String configPath;
	private String basePath;
	private String outputPath;
	private String filename;

	private Set<String> selectedFeatures;
	private boolean sourceFilesAdded;
	private Set<String> featureNames;

	public void run() {

		DJIdeProperties.changeValidationStatus(ValidationStatus.VALIDATE_ALL);
		DJStandaloneCompiler compiler = new DJStandaloneCompiler(filename);
		String uriPrefix = getUriPrefix();
		boolean error;
		try {
			error = compiler.compile(basePath, outputPath, uriPrefix);
		} catch (Exception e) {

			error = true;
		}
		if (error)
			DeltajCorePlugin.getDefault().logWarning("error: " + compiler.getErrorReport());
		try {
			ResourcesPlugin.getWorkspace().getRoot()
					.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			DeltajCorePlugin.getDefault().logError(e);
		}

	}

	@Override
	public void performFullBuild(IFile config) {

		assert (featureProject != null) : "Invalid project given";

		configPath = config.getRawLocation().toOSString();
		basePath = featureProject.getSourcePath().replace('\\', '/') + "/";
		outputPath = featureProject.getBuildPath().replace('\\', '/') + "/";

		if (configPath == null || basePath == null || outputPath == null)
			return;

		Configuration configuration = new Configuration(
				featureProject.getFeatureModel());
		ConfigurationReader reader = new ConfigurationReader(configuration);
		try {
			reader.readFromFile(config);
		} catch (CoreException e) {
			DeltajCorePlugin.getDefault().logError(e);
		} catch (IOException e) {
			DeltajCorePlugin.getDefault().logError(e);
		}
		updateSelectedFeatures(configuration);

		featureNames = configuration.getFeatureModel().getFeatureNames();
		sourceFilesAdded = false;

		try {
			handleSourceFiles(featureProject.getSourceFolder());
		} catch (CoreException e) {
			DeltajCorePlugin.getDefault().logError(e);
		}

		if (!sourceFilesAdded) {

			return;
		}

		run();
	}

	private void updateSelectedFeatures(Configuration configuration) {
		selectedFeatures = new TreeSet<String>();

		for (Feature feature : configuration.getSelectedFeatures()) {

			selectedFeatures.add(feature.getName());
		}
	}

	@Override
	public LinkedHashSet<String> extensions() {
		LinkedHashSet<String> extensions = new LinkedHashSet<String>();
		extensions.add("dj");
		return extensions;
	}

	@Override
	public void copyNotComposedFiles(IFile config, IFolder destination) {
		copyFolderMembers(featureProject.getSourceFolder());
	}

	private void copyFolderMembers(IFolder folder) {

		try {
			for (IResource res : folder.members()) {
				if (!extensions().contains(res.getFileExtension())) {
					res.copy(new Path(featureProject.getBuildFolder()
							.getFullPath().toString()
							+ "/" + res.getName()), true, null);
				}
				if (res instanceof IFolder) {
					copyFolderMembers((IFolder) res);
				}
			}
		} catch (CoreException e) {
			DeltajCorePlugin.getDefault().logError(e);
		}
	}
	
	@Override
	public ArrayList<String[]> getTemplates() {
		return TEMPLATES;
	}

	private static final ArrayList<String[]> TEMPLATES = createTempltes();
	
	private static ArrayList<String[]> createTempltes() {
		 ArrayList<String[]> list = new  ArrayList<String[]>(2);
		 list.add(new String[]{"DeltaJ (Core Module)", "dj", "features " + FEATUE_PATTER + "\nconfigurations\n" + FEATUE_PATTER + ";\n\n\ncore " + FEATUE_PATTER + " {\n\tclass " + CLASS_NAME_PATTERN + "{\n\n\t}\n}" });
		 list.add(new String[]{"DeltaJ (Delta Module)", "dj", "delta " + FEATUE_PATTER + " when " + FEATUE_PATTER + " {\n\tmodifies class " + CLASS_NAME_PATTERN + "{\n\n\t}\n}"});
		 
		 return list;
	}

	@Override
	public int getDefaultTemplateIndex() {
		return 1;
	}

	@Override
	public boolean hasFeatureFolders() {
		return false;
	}

	private String getUriPrefix() {
		String uriPrefix = "platform:/resource/"
				+ featureProject.getProjectName() + "/"
				+ featureProject.getProjectSourcePath() + "/";
		return uriPrefix;
	}

	private void handleSourceFiles(IFolder folder) throws CoreException {

		for (IResource res : folder.members()) {

			if (res instanceof IFile) {
				if (res.getName().endsWith(".dj")) {
					updateFile(((IFile) res).getRawLocation().toFile());
					res.refreshLocal(IResource.DEPTH_ZERO, null);
					filename = res.getName();
					sourceFilesAdded = true;
				}

			}
		}
	}

	private void updateFile(final File file) {

		String newFileText = null;
		String oldFileText = fileToString(file.getAbsolutePath());
		if (isCoreFile(oldFileText)) {

			newFileText = getNewFileStringCore(file);

		} else if (isDeltaFile(oldFileText)) {

			newFileText = getNewFileStringDelta(file);
		}
		if (newFileText!=null&&!newFileText.equals(oldFileText))
			saveStringToFile(newFileText, file);
	}

	private String getImportsString(String fileName) {
		IFolder folder = featureProject.getSourceFolder();
		StringBuilder strBuf = new StringBuilder();

		try {
			for (IResource res : folder.members()) {
				if (res instanceof IFile) {
					String resourceName = res.getName();
					if (resourceName.endsWith(".dj")
							&& !resourceName.equals(fileName)) {
						strBuf.append("import \"");
						strBuf.append(resourceName);
						strBuf.append("\"\n");
					}

				}
			}
			strBuf.append("\n");
		} catch (CoreException e) {
			DeltajCorePlugin.getDefault().logError(e);
		}

		return strBuf.toString();
	}

	private static Matcher getMatcherFromFileTextCore(String fileText) {

		String patternString = "^(.*)features(.*)configurations(.*)core(.*?)\\{(.*)\\}.*$";
		Pattern pattern = Pattern.compile(patternString, Pattern.DOTALL);
		return pattern.matcher(fileText);

	}

	private Matcher getMatcherFromFileTextDelta(String fileText) {
		String patternString = "(.*)delta(.*)";
		Pattern pattern = Pattern.compile(patternString, Pattern.DOTALL);

		return pattern.matcher(fileText);

	}

	private void saveStringToFile(String text, File file) {
		if (text == null || text.equals(""))
			return;
		FileWriter fw = null;
		try {
			fw = new FileWriter(file);
			fw.write(text);

		} catch (IOException e) {
			DeltajCorePlugin.getDefault().logError(e);

		} finally {
			if (fw != null) {
				try {
					fw.close();
				} catch (IOException e) {

					DeltajCorePlugin.getDefault().logError(e);
				}
			}
		}

	}

	private boolean isCoreFile(String fileText) {
		Matcher matcher = getMatcherFromFileTextCore(fileText);
		return matcher.matches();
	}

	private boolean isDeltaFile(String fileText) {
		Matcher matcher = getMatcherFromFileTextDelta(fileText);
		return matcher.matches();
	}

	private String getNewFileStringDelta(File file) {
		String fileString = fileToString(file.getAbsolutePath());

		Matcher matcher = getMatcherFromFileTextDelta(fileString);

		StringBuilder buf = new StringBuilder(fileString);
		if (matcher.matches())
			buf.replace(matcher.start(1), matcher.end(1),
					getImportsString(file.getName()));

		return buf.toString();
	}

	private String getNewFileStringCore(File file) {
		String fileString = fileToString(file.getAbsolutePath());
		Matcher matcher = getMatcherFromFileTextCore(fileString);
		matcher.matches();
		StringBuilder buf = new StringBuilder(matcher.group(0));
		String configurationString = getConfigurationString(selectedFeatures);
		String features = getFeatureString(featureNames);

		buf.replace(matcher.start(2), matcher.end(2), features + "\n");
		Matcher matcher2 = getMatcherFromFileTextCore(buf.toString());
		matcher2.matches();
		buf.replace(matcher2.start(3), matcher2.end(3), configurationString
				+ "\n");

		buf.replace(0, buf.indexOf("features"),
				getImportsString(file.getName()));

		return buf.toString();

	}

	private String getFeatureString(Set<String> selectedFeatures) {
		Configuration configuration = new Configuration(
				featureProject.getFeatureModel());
		updateSelectedFeatures(configuration);
		StringBuilder features = new StringBuilder();

		for (String s : selectedFeatures) {
			features.append(" " + s + ",");
		}

		features.deleteCharAt(features.length() - 1);

		return features.toString();
	}

	private String getConfigurationString(Set<String> selectedFeatures) {

		return getFeatureString(selectedFeatures).concat(";");
	}

	private static String fileToString(String filePath) {
		byte[] buffer = new byte[(int) new File(filePath).length()];
		FileInputStream f = null;
		try {
			f = new FileInputStream(filePath);
			f.read(buffer);
		} catch (FileNotFoundException e) {
			DeltajCorePlugin.getDefault().logError(e);
		} catch (IOException e) {
			DeltajCorePlugin.getDefault().logError(e);
		} finally {
			if (f != null)
				try {
					f.close();
				} catch (IOException e) {
					DeltajCorePlugin.getDefault().logError(e);
				}

		}

		return new String(buffer);
	}

	@Override
	public void postCompile(IResourceDelta delta, final IFile file) {
		Job job = new Job("Propagate problem markers") {
			@Override
			public IStatus run(IProgressMonitor monitor) {
				try {
					if (file.exists() && !extensions().contains(file.getFileExtension())) {
						IMarker[] markers = file.findMarkers(null, false,
								IResource.DEPTH_ZERO);
						if (markers.length!=0) {
							for (IMarker marker : markers) {
								if (marker.exists()) {

									IResource res = featureProject
											.getSourceFolder().findMember(
													file.getName());
									if (res != null) {
										IMarker newMarker = res
												.createMarker(CorePlugin.PLUGIN_ID
														+ ".builderProblemMarker");
										newMarker.setAttributes(marker
												.getAttributes());
									}

								} else {
									marker.delete();
								}
							}
						}
					}

				} catch (CoreException e) {
					DeltajCorePlugin.getDefault().logError(e);
				}
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.DECORATE);
		job.schedule();
	}

	@Override
	public boolean hasCustomFilename() {
		return true;
	}

}
