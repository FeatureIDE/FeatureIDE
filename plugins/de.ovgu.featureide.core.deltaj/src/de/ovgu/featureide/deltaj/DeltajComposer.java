package de.ovgu.featureide.deltaj;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.xtext.example.util.DJIdeProperties;
import org.xtext.example.util.ValidationStatus;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationReader;
import djtemplates.DJStandaloneCompiler;

/**
 * DeltaJava Composer
 * 
 * @author Fabian Benduhn
 */
public class DeltajComposer implements IComposerExtensionClass {
	public static final String JAVA_NATURE = "org.eclipse.jdt.core.javanature";
	private String equationPath;
	private String basePath;
	private String outputPath;
	private String filename;
	private IFeatureProject featureProject = null;

	private Set<String> selectedFeatures;
	private Boolean sourceFilesAdded;
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
			System.out.println("error: " + compiler.getErrorReport());
		try {
			ResourcesPlugin.getWorkspace().getRoot()
					.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			DeltajCorePlugin.getDefault().logError(e);
		}

	}

	@Override
	public void initialize(IFeatureProject project) {

		featureProject = project;

	}

	@Override
	public void performFullBuild(IFile equation) {

		assert (featureProject != null) : "Invalid project given";

		equationPath = equation.getRawLocation().toOSString();
		basePath = featureProject.getSourcePath().replace('\\', '/') + "/";
		outputPath = featureProject.getBuildPath().replace('\\', '/') + "/";

		if (equationPath == null || basePath == null || outputPath == null)
			return;

		Configuration configuration = new Configuration(
				featureProject.getFeatureModel());
		ConfigurationReader reader = new ConfigurationReader(configuration);
		try {
			reader.readFromFile(equation);
		} catch (CoreException e) {
			DeltajCorePlugin.getDefault().logError(e);
		} catch (IOException e) {
			DeltajCorePlugin.getDefault().logError(e);
		}
		updateSelectedFeatures(configuration);

		featureNames = configuration.getFeatureModel().getFeatureNames();
		sourceFilesAdded = false;

		try {
			addSourceFiles(featureProject.getSourceFolder());
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
	public ArrayList<String> extensions() {
		ArrayList<String> extensions = new ArrayList<String>();
		extensions.add(".dj");
		return extensions;
	}

	public String getEditorID(String extension) {
		if (extension.equals("dj")) {

			return "org.eclipse.jdt.ui.CompilationUnitEditor";
		}
		return "";
	}

	@Override
	public void clean() {

	}

	@Override
	public boolean copyNotComposedFiles() {

		return true;
	}

	@Override
	public boolean composerSpecficMove(IFolder source, IFolder destination) {

		return false;
	}

	@Override
	public void buildFSTModel() {

	}

	@Override
	public ArrayList<String[]> getTemplates() {

		String[] core = { "DeltaJ Core Module", "dj",
				"features #featurename#\nconfigurations\n#featurename#;\n\n\ncore #featurename# {\n\tclass #classname#{\n\n\t}\n}" };
		String[] delta = { "DeltaJ Delta Module", "dj", "delta #featurename# when #featurename#{\n\tmodifies class #classname#{\n\n\t}\n}"  };
		ArrayList<String[]> list = new ArrayList<String[]>();
		list.add(core);
		list.add(delta);
		return list;
	}

	@Override
	public void addCompiler(IProject project, String sourcePath,
			String equationPath, String buildPath) {
	}

	@Override
	public boolean hasFeatureFolders() {

		return false;
	}

	static Matcher getMatcherFromFileText(String fileText) {

		String patternString = "^(.*)features(.*)configurations(.*)core(.*?)\\{(.*)\\}.*$";
		Pattern pattern = Pattern.compile(patternString, Pattern.DOTALL);
		return pattern.matcher(fileText);

	}

	private String getUriPrefix() {
		String uriPrefix = "platform:/resource/"
				+ featureProject.getProjectName() + "/"
				+ featureProject.getProjectSourcePath() + "/";
		return uriPrefix;
	}

	private void addSourceFiles(IFolder folder) throws CoreException {

		for (IResource res : folder.members()) {

			if (res instanceof IFolder) {
				addSourceFiles((IFolder) res);
			} else if (res instanceof IFile) {
				if (res.getName().endsWith(".dj")) {
					updateConfiguration(((IFile) res).getRawLocation().toFile());

				}
				filename = res.getName();
				sourceFilesAdded = true;
			}
		}
	}

	private void updateConfiguration(final File file) {
		Job job = new Job("update Configuration") {
			@Override
			public IStatus run(IProgressMonitor monitor) {
				if (isCoreFile(file)) {
					String newFileText = getNewFileString(file);

					SaveStringToFile(newFileText, file);
				}
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.DECORATE);
		job.schedule();
		

	}

	private void SaveStringToFile(String text, File file) {
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

	private boolean isCoreFile(File file) {
		Matcher matcher = getMatcherFromFile(file);
		return matcher.matches();
	}

	private String getNewFileString(File file) {
		Matcher matcher = getMatcherFromFile(file);
		matcher.matches();
		StringBuffer buf = new StringBuffer(matcher.group(0));
		String configurationString = getConfigurationString(selectedFeatures);
		String features = getFeatureString(featureNames);

		buf.replace(matcher.start(2), matcher.end(2), features + "\n");
		Matcher matcher2 = getMatcherFromFileText(buf.toString());
		matcher2.matches();
		buf.replace(matcher2.start(3), matcher2.end(3), "\n"
				+ configurationString + "\n");

		return buf.toString();

	}

	private String getFeatureString(Set<String> selectedFeatures) {
		Configuration configuration = new Configuration(
				featureProject.getFeatureModel());
		updateSelectedFeatures(configuration);
		StringBuffer features = new StringBuffer();

		for (String s : selectedFeatures) {
			features.append(" " + s + ",");
		}

		features.deleteCharAt(features.length() - 1);

		return features.toString();
	}

	private String getConfigurationString(Set<String> selectedFeatures) {

		return getFeatureString(selectedFeatures).concat(";");
	}

	private static Matcher getMatcherFromFile(File file) {
		String fileText = fileToString(file.getAbsolutePath());
		return getMatcherFromFileText(fileText);
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
	public void postCompile(IFile file) {

	}

	@Override
	public String replaceMarker(String text, List<String> list) {

		return text;
	}
	
}
