package de.ovgu.featureide.core.aspectj;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Scanner;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationReader;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelWriter;

/**
 * Excludes unselected aspects form buildpath.
 * 
 * @author Jens Meinicke
 */
public class AspectJComposer implements IComposerExtensionClass {

	private static final String JAVA_NATURE = "org.eclipse.jdt.core.javanature";
	private static final String ASPECTJ_NATURE = "org.eclipse.ajdt.ui.ajnature";
	
	private static final String NEW_ASPECT = "\t// TODO Auto-generated aspect\r\n";

	private static final String XML_HEAD = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\r\n";
	private static final String START_ENTRY = "<classpath>";
	private static final String EXCLUDE_ENTRY = "\t<classpathentry excluding=\"";
	private static final String EXCLUDE_SOURCE_ENTRY = "\" kind=\"src\" path=\"";
	private static final String SOURCE_ENTRY = "\t<classpathentry kind=\"src\" path=\"";
	private static final String CONTAINER_ENTRY = "\t<classpathentry kind=\"con\" path=\"";
	private static final String ASPECTJRT_CONTAINER = "org.eclipse.ajdt.core.ASPECTJRT_CONTAINER";
	private static final String JRE_CONTAINER = "org.eclipse.jdt.launching.JRE_CONTAINER";
	private static final String OUTPUT_ENTRY = "\t<classpathentry kind=\"output\" path=\"";
	private static final String END_ENTRY = "</classpath>";
	
	private IFeatureProject featureProject;
	private LinkedList<String> selectedFeatures;
	private LinkedList<String> unSelectedFeatures;
	private FeatureModel featureModel;
	private boolean hadAspectJNature;
	
	@Override
	public ArrayList<String> extensions() {
		ArrayList<String> extensions = new ArrayList<String>();
		extensions.add(".java");
		return extensions;
	}

	@Override
	public String getEditorID(String extension) {
		return "";
	}

	@Override
	public void initialize(IFeatureProject project) {
		featureProject = project;
	}

	@Override
	public void performFullBuild(IFile config) {
		if (config == null) {
			return;
		}
		assert(featureProject != null) : "Invalid project given";
		
		final String configPath =  config.getRawLocation().toOSString();
		final String outputPath = featureProject.getBuildPath();
		
		if (configPath == null || outputPath == null)
			return;
		
		Configuration configuration = new Configuration(featureProject.getFeatureModel());
		ConfigurationReader reader = new ConfigurationReader(configuration);
		
		try {
			reader.readFromFile(config);
		} catch (CoreException e) {
			AspectJCorePlugin.getDefault().logError(e);
		} catch (IOException e) {
			AspectJCorePlugin.getDefault().logError(e);
		}
		selectedFeatures = new LinkedList<String>();
		unSelectedFeatures = new LinkedList<String>();
		for (Feature feature : configuration.getSelectedFeatures()) {
			selectedFeatures.add(feature.getName());
		}
		for (Feature feature : featureProject.getFeatureModel().getLayers()) {
			if (!selectedFeatures.contains(feature.getName())) {
				unSelectedFeatures.add(feature.getName());
			}
		}
		
		setBuildpaths(config.getProject());
		try {
			config.getProject().refreshLocal(IResource.DEPTH_INFINITE, null);
			featureProject.getProject().build(IncrementalProjectBuilder.FULL_BUILD,	null);
		} catch (CoreException e) {
			AspectJCorePlugin.getDefault().logError(e);
		}
	}

	private void setBuildpaths(IProject project) {
		Scanner scanner = null;
		FileWriter fw = null;
		IFile iClasspathFile = project.getFile(".classpath");
		try {
			File file = iClasspathFile.getRawLocation().toFile();
			StringBuffer fileText = new StringBuffer();
			scanner = new Scanner(file);
			while (scanner.hasNext()) {
				String line = scanner.nextLine();
				if (line.contains(START_ENTRY)) {
					fileText.append(line);
					fileText.append("\r\n");
					break;
				} else {
					fileText.append(line);
					fileText.append("\r\n");
				}
			}
			
			while (scanner.hasNext()) {
				String line = scanner.nextLine();
				if (line.equals(END_ENTRY)) {
					break;
				}
				if (line.contains(EXCLUDE_ENTRY) || line.contains(SOURCE_ENTRY)) {
					fileText.append(createEntry(line));
					fileText.append("\r\n");
				} else {
					fileText.append(line);
					fileText.append("\r\n");
				}
			}
			
			String fileTextString = fileText.toString();			
			fileTextString = fileTextString + END_ENTRY;
			fw = new FileWriter(file);
			fw.write(fileTextString);
			iClasspathFile.refreshLocal(IResource.DEPTH_ZERO, null);
		} catch (FileNotFoundException e) {
			AspectJCorePlugin.getDefault().logError(e);
		} catch (IOException e) {
			AspectJCorePlugin.getDefault().logError(e);
		} catch (CoreException e) {
			AspectJCorePlugin.getDefault().logError(e);
		} finally {
			if(scanner!=null)
			scanner.close();
			if(fw!=null) {
				try {
					fw.close();
				} catch (IOException e) {
					AspectJCorePlugin.getDefault().logError(e);
				}	
			}
		}
	}
	
	private String createEntry(String line) {
		String entry = null;
		if (!line.contains(SOURCE_ENTRY)) {
			for (String oldEntry : getOldEntrys(line)) {
				if (!oldEntry.endsWith(".aj")) {
					if (entry == null) {
						entry = oldEntry;
					} else {
						entry = entry + "|" + oldEntry;
					}
				}
			}
		}
		for (String excludedFeature : unSelectedFeatures) {
			if (entry == null) {
				entry = excludedFeature.replaceAll("_", "/") + ".aj";
			} else {
				entry = entry + "|" + excludedFeature.replaceAll("_", "/") + ".aj";
			}
		}
		if (entry != null) {
			return EXCLUDE_ENTRY + entry + EXCLUDE_SOURCE_ENTRY + featureProject.getBuildFolder().getProjectRelativePath() + "\"/>";
		} else {
			return SOURCE_ENTRY + featureProject.getBuildFolder().getName() + "\"/>";
		}
	}

	private String[] getOldEntrys(String line) {
		line = line.substring(line.indexOf("\"") + 1);
		line = line.replace(EXCLUDE_SOURCE_ENTRY + featureProject.getBuildFolder().getProjectRelativePath() + "\"/>", "");
		return line.split("[|]");
	}

	@Override
	public boolean clean() {
		return false;
	}

	@Override
	public boolean copyNotComposedFiles() {
		return true;
	}

	@Override
	public boolean postAddNature(IFolder source, IFolder destination) {
		CorePlugin.getDefault().addProject(source.getProject());
		addNatures(source.getProject());
		setClasspathFile(source.getProject());
		if (hadAspectJNature) {
			createFeatureModel(CorePlugin.getFeatureProject(source));
		}
		try {
			source.getProject().refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			AspectJCorePlugin.getDefault().logError(e);
		}
		return true;
	}

	private void createFeatureModel(IFeatureProject project) {
		if (project == null) {
			return;
		}
		if (project.getFeatureModel() == null) {
			return;
		}
		featureModel = project.getFeatureModel(); 
		try {
			if (addAspects(project.getBuildFolder(), "")) {
				featureModel.getRoot().removeChild(featureModel.getFeature("Base"));
				Feature root = featureModel.getRoot();
				root.setName("Base");
				featureModel.setRoot(root);
				featureModel.getRoot().setAbstract(false);
				XmlFeatureModelWriter w = new XmlFeatureModelWriter(featureModel);
				w.writeToFile(project.getProject().getFile("model.xml"));
				project.getProject().getFile("model.xml").refreshLocal(IResource.DEPTH_ZERO, null);
			}
		} catch (CoreException e) {
			AspectJCorePlugin.getDefault().logError(e);
		}
	}

	private boolean addAspects(IFolder folder, String folders) throws CoreException {
		boolean hasAspects = false;
		for (IResource res : folder.members()) {
			if (res instanceof IFolder) {
				hasAspects = addAspects((IFolder)res, folders + res.getName() + "_");
			} else if (res instanceof IFile) {
				if (res.getName().endsWith(".aj")) {
					Feature feature = new Feature(featureModel, folders + res.getName().split("[.]")[0]);
					featureModel.getRoot().addChild(feature);
					hasAspects = true;
				}
			}
		}
		return hasAspects;
	}

	private void setClasspathFile(IProject project) {
		Scanner scanner = null;
		FileWriter fw = null;
		IFile iClasspathFile = project.getFile(".classpath");
		if (!iClasspathFile.exists()) {
			addClasspathFile(project, null);
		} else {
			try {
				File file = iClasspathFile.getRawLocation().toFile();
				StringBuffer fileText = new StringBuffer();
				scanner = new Scanner(file);
				while (scanner.hasNext()) {
					String line = scanner.nextLine();
					if (line.contains(END_ENTRY)) {
						break;
					} 
					fileText.append(line);
					fileText.append("\r\n");
				}
				
				String fileTextString = fileText.toString();
				if (!fileTextString.contains(ASPECTJRT_CONTAINER)) {
					fileTextString = fileTextString + CONTAINER_ENTRY + ASPECTJRT_CONTAINER + "\"/>\r\n";
				}
				if (!fileTextString.contains(JRE_CONTAINER)) {
					fileTextString = fileTextString + CONTAINER_ENTRY + JRE_CONTAINER + "\"/>\r\n";
				}
				fileTextString = fileTextString + END_ENTRY;
				fw = new FileWriter(file);
				fw.write(fileTextString);
				
			} catch (FileNotFoundException e) {
				AspectJCorePlugin.getDefault().logError(e);
			} catch (IOException e) {
				AspectJCorePlugin.getDefault().logError(e);
			} finally {
				if(scanner!=null)
				scanner.close();
				if(fw!=null) {
					try {
						fw.close();
					} catch (IOException e) {
						AspectJCorePlugin.getDefault().logError(e);
					}	
				}
			}
		}
	}

	@Override
	public void addCompiler(IProject project, String sourcePath,
			String configPath, String buildPath) {
		addNatures(project);
		addClasspathFile(project, buildPath);
	}

	private void addClasspathFile(IProject project, String buildpath) {
		if (buildpath == null) {
			if (featureProject == null || featureProject.getBuildPath() == null) {
				buildpath = IFeatureProject.DEFAULT_SOURCE_PATH;
			} else {
				buildpath = featureProject.getBuildPath().toString();
			}
		}
		IFile iClasspathFile = project.getFile(".classpath");
		if (!iClasspathFile.exists()) {
			String bin = "bin";
			try {
				String text = XML_HEAD + 
			 				  START_ENTRY + "\r\n" +
			 				  SOURCE_ENTRY + buildpath + "\"/>\r\n" +
			 				  CONTAINER_ENTRY + ASPECTJRT_CONTAINER + "\"/>\r\n" +
			 				  CONTAINER_ENTRY + JRE_CONTAINER + "\"/>\r\n" +
			 				  OUTPUT_ENTRY + bin + "\"/>\r\n" + 
			 				  END_ENTRY; 
				InputStream source = new ByteArrayInputStream(text.getBytes());
				iClasspathFile.create(source, true, null);
			} catch (CoreException e) {
				AspectJCorePlugin.getDefault().logError(e);
			}

		}
	}

	private void addNatures(IProject project) {
		try {
			if (!project.isAccessible()) {
				return;
			}
			
			int i = 2;
			if (project.hasNature(JAVA_NATURE)) {
				i--;
			}
			hadAspectJNature = project.hasNature(ASPECTJ_NATURE);
			if (hadAspectJNature) {
				i--;
			}
			if (i == 0) {
				return;
			}
			IProjectDescription description = project.getDescription();
			String[] natures = description.getNatureIds();
			String[] newNatures = new String[natures.length + i];
			int j = 2;
			newNatures[0] = ASPECTJ_NATURE;
			newNatures[1] = JAVA_NATURE;
			for (String nature : natures) {
				if (!(nature.equals(ASPECTJ_NATURE) || nature.equals(JAVA_NATURE))) {
					newNatures[j] = nature;
					j++;
				}
			}
			description.setNatureIds(newNatures);
			project.setDescription(description, null);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	@Override
	public void buildFSTModel() {
	}

	@Override
	public ArrayList<String[]> getTemplates() {
		ArrayList<String[]> list = new ArrayList<String[]>();
		String[] java = {"Java", "java", "public class #classname# {\n\n}"};
		list.add(java);
		return list;
	}

	@Override
	public String replaceMarker(String text, List<String> list) {
		return null;
	}

	@Override
	public void postCompile(IResourceDelta delta, IFile file) {
	}

	@Override
	public boolean hasFeatureFolders() {
		return false;
	}

	private String rootName = "";
	
	@Override
	public void postModelChanged() {
		try {
			featureProject.getProject().refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			AspectJCorePlugin.getDefault().logError(e);
		}
		Feature root = featureProject.getFeatureModel().getRoot();
		if (root == null) {
			return;
		}
		rootName = root.getName();
		if (root != null && !rootName.equals("") && root.hasChildren()) {
			checkAspect(root);
		}
	}

	private void checkAspect(Feature feature) {
		if (feature.hasChildren()) {
			for (Feature child : feature.getChildren()) {
				if (child.isLayer() && !child.getName().equals(rootName)) {
					try {
						createAspect(child.getName(), featureProject.getBuildFolder(), null);
					} catch (CoreException e) {
						AspectJCorePlugin.getDefault().logError(e);
					}
				}
				checkAspect(child);
			}
		}
	}

	public static IFile getAspectFile(String aspect, String aspectPackage, IFolder folder) {
		String text = aspect.split("[_]")[0];
		if (aspect.contains("_")) {
			if (aspectPackage == null) {
				aspectPackage = text; 
			} else {
				aspectPackage = aspectPackage + "." + text;
			}
			return getAspectFile(aspect.substring(text.length() + 1), aspectPackage, folder.getFolder(text));
		} else {
			try {
				createFolder(folder);
			} catch (CoreException e) {
				AspectJCorePlugin.getDefault().logError(e);
			}
			return folder.getFile(text + ".aj");
		}
	}
 
	private void createAspect(String aspect, IFolder folder, String aspectPackage) throws CoreException {
		IFile aspectFile = getAspectFile(aspect, aspectPackage, folder);
		if (aspectPackage == null && aspect.contains("_")) {
			aspectPackage = aspect.substring(0, aspect.lastIndexOf("_")).replaceAll("_", ".");
			aspect = aspect.substring(aspect.lastIndexOf("_") + 1);
		}
		if (!aspectFile.exists()) {
			String fileText;
			if (aspectPackage != null) {
				fileText = "\r\n" +
						   "package " + aspectPackage + ";\r\n" +
						   "\r\n" +
						   "public aspect " + aspect + " {\r\n" + 
						   NEW_ASPECT +
						   "}"; 
			} else {
				fileText = "\r\n" +
						   "public aspect " + aspect + " {\r\n" + 
						   NEW_ASPECT +
						   "}"; 
			}
			InputStream source = new ByteArrayInputStream(fileText.getBytes());
			aspectFile.create(source, true, null);
			aspectFile.refreshLocal(IResource.DEPTH_ZERO, null);
		}
	}

	public static void createFolder(IFolder folder) throws CoreException {
		if (!folder.exists()) {
			createFolder((IFolder)folder.getParent());
			folder.create(true, true, null);
		}
	}

	@Override
	public int getDefaultTemplateIndex() {
		return 0;
	}

	@Override
	public boolean hasCustomFilename() {
		return false;
	}

	@Override
	public boolean hasFeatureFolder() {
		return false;
	}

}
