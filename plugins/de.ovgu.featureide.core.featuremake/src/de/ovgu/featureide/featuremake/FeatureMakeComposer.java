package de.ovgu.featureide.featuremake;

import static de.ovgu.featureide.fm.core.localization.StringTable.C_HEADER_FILE;
import static de.ovgu.featureide.fm.core.localization.StringTable.IS_NOT_INSTALLED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.PREPROCESSOR_ANNOTATION_CHECKING;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_REQUIRED_BUNDLE;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.Stack;
import java.util.Vector;
import java.util.regex.Pattern;

import org.eclipse.cdt.core.CCorePlugin;
import org.eclipse.cdt.core.model.CoreModel;
import org.eclipse.cdt.core.settings.model.ICProjectDescription;
import org.eclipse.cdt.core.settings.model.ICProjectDescriptionManager;
import org.eclipse.cdt.managedbuilder.core.BuildException;
import org.eclipse.cdt.managedbuilder.core.IConfiguration;
import org.eclipse.cdt.managedbuilder.core.IManagedBuildInfo;
import org.eclipse.cdt.managedbuilder.core.IManagedProject;
import org.eclipse.cdt.managedbuilder.core.IProjectType;
import org.eclipse.cdt.managedbuilder.core.ManagedBuildManager;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.prop4j.And;
import org.prop4j.Node;
import org.prop4j.Not;

//import br.ufal.ic.colligens.activator.Colligens;
//import br.ufal.ic.colligens.controllers.core.CPPModelBuilder;
//import br.ufal.ic.colligens.controllers.core.CPPWrapper;
//import br.ufal.ic.colligens.controllers.invalidproducts.InvalidProductsViewController;
//import br.ufal.ic.colligens.util.InvalidProductViewLog;
//import br.ufal.ic.colligens.util.ProjectConfigurationErrorLogger;
import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.builder.preprocessor.PPComposerExtensionClass;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.FileReader;

public class FeatureMakeComposer extends PPComposerExtensionClass {

	private static final String PLUGIN_CDT_ID = "org.eclipse.cdt";
	private static final String PLUGIN_WARNING = THE_REQUIRED_BUNDLE + PLUGIN_CDT_ID + IS_NOT_INSTALLED_;
	public static final String COMPOSER_ID = FeatureMakeCorePlugin.PLUGIN_ID + ".cppcomposer";
	public static final String C_NATURE = "org.eclipse.cdt.core.cnature";
	public static final String MANAGED_NATURE = "org.eclipse.cdt.managedbuilder.core.managedBuildNature";
	public static final String SCANNER_NATURE = "org.eclipse.cdt.managedbuilder.core.ScannerConfigNature";
	private static final String FEATURE_MAKE_CONFIG_ID = FeatureMakeCorePlugin.PLUGIN_ID + ".configuration";
	private static final String FEATURE_MAKE_CONFIG_NAME = "FeatureMake Configuration";
	private static final String DEFAULT_PROJECT_GNU_TYPE = "cdt.managedbuild.target.gnu.exe";
	private static final String DEFAULT_TOOLCHAIN_DEBUG = "cdt.managedbuild.target.gnu.platform.exe.debug";
	private static final String DEFAULT_TOOLCHAIN_RELEASE = "cdt.managedbuild.target.gnu.platform.exe.release";
	
	private IConfiguration buildConfiguration;
	/* pattern for replacing preprocessor commands like "//#if" */
	static final Pattern replaceCommandPattern = Pattern.compile("#(.+?)\\s");

	private CPPModelBuilder cppModelBuilder;

	/*
	 * If the user runs the compileAllProducs and the typechef warn about errors
	 * in the project the user needs to choose if want to continue with the
	 * compilation
	 */
	private static boolean continueCompilationFlag = true;
	/* manage the compilation execution */
	private static Set<Long> threadInExecId = new HashSet<Long>();

	public FeatureMakeComposer() {
		super("CppMakeComposer");
	}

	@Override
	public boolean hasSourceFolder() {
		return true;
	}
	

	@Override
	public boolean initialize(IFeatureProject project) {
		boolean supSuccess = super.initialize(project);
		cppModelBuilder = new CPPModelBuilder(project);
		
		prepareFullBuild(null);
		annotationChecking();
		createCdtProjectDescription(project.getProject());
		
		if (supSuccess == false || cppModelBuilder == null) {
			return false;
		} else {
			return true;
		}
	}

	private static final LinkedHashSet<String> EXTENSIONS = createExtensions();

	private static LinkedHashSet<String> createExtensions() {
		LinkedHashSet<String> extensions = new LinkedHashSet<String>();
		extensions.add("h");
		extensions.add("c");
		return extensions;
	}

	@Override
	public LinkedHashSet<String> extensions() {
		return EXTENSIONS;
	}

	@Override
	public void addCompiler(IProject project, String sourcePath, String configPath, String buildPath) {
		addNature(project);
	}

	private void addNature(IProject project) {
		try {
			if (!project.isAccessible() || project.hasNature(C_NATURE))
				return;
			
			IProjectDescription description = project.getDescription();
			List<String> natures = new ArrayList<String>(Arrays.asList(description.getNatureIds()));
			natures.add(C_NATURE);
			natures.add(MANAGED_NATURE);
			natures.add(SCANNER_NATURE);
			description.setNatureIds(natures.toArray(new String[natures.size()]));
			project.setDescription(description, null);
			

		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}

	}
	
	private String getIfDefCodeForFeature(IFeature feature,StringBuilder sb){
		String newLine = System.lineSeparator();
		
		sb.append("#ifndef ").append(feature.getName()).append(newLine);
		sb.append("\t#define ").append(feature.getName()).append(newLine);
		sb.append("#endif /* ").append(feature.getName()).append(" */").append(newLine).append(newLine);
		
		return sb.toString();
	}
	
	private void createProjectDefinitionHeaderFile(String content,String folder){
		
		IFile file = featureProject.getProject().getFile(folder + "projectdefs.h");
		
		InputStream fileStream = new ByteArrayInputStream(content.getBytes());
		if(file.exists()){
			// delete the file if exist and create new
			try {
				file.delete(true, new NullProgressMonitor());
			} catch (CoreException e1) {
				e1.printStackTrace();
			}
			try {
				file.create(fileStream, false, new NullProgressMonitor());
				fileStream.close();
			} catch (CoreException | IOException e) {
				e.printStackTrace();
			}
		}
		else{
			try {
				file.create(fileStream, false, new NullProgressMonitor());
				fileStream.close();
			} catch (CoreException | IOException e) {
				e.printStackTrace();
			}
		}
		try {
			file.setDerived(true,null);
		} catch (CoreException e2) {
			e2.printStackTrace();
		}
	}
	
	private void createProjectDefinitionsByFeatures(List<IFeature> features,String folderName){
		StringBuilder sb = new StringBuilder();
		String newLine = System.lineSeparator();
		// preamble
		sb.append("/* This files is generated by FeatureMake, do not update this file! */"+newLine);
		sb.append("#ifndef SOURCE_PROJECTDEFS_H_"+newLine).append("#define SOURCE_PROJECTDEFS_H_"+newLine);
		
		for (IFeature feature : features) {
			IFeatureStructure structure = feature.getStructure();
			
			if (structure.isConcrete()) {
				StringBuilder sbIfDef = new StringBuilder();
				sb.append(getIfDefCodeForFeature(feature, sbIfDef));
			}
		}
		sb.append("#endif /* SOURCE_PROJECTDEFS_H_ */");
		
		createProjectDefinitionHeaderFile(sb.toString(),folderName);
	}
	
	@Override
	public void performFullBuild(IFile config) {

		prepareFullBuild(config);
		IFeatureModel model = CorePlugin.getFeatureProject(config).getFeatureModel();
		Configuration cfg = new Configuration(model);
		final FileReader<de.ovgu.featureide.fm.core.configuration.Configuration> reader = new FileReader<>(Paths.get(config.getLocationURI()), cfg,
				ConfigurationManager.getFormat(config.getName()));
		reader.read();
		
		createProjectDefinitionsByFeatures(cfg.getSelectedFeatures(), "source/");

		
		annotationChecking();
	}
	
	private void createCdtProjectDescription(IProject project){
		
		ICProjectDescription projDesc = null;		
		ICProjectDescriptionManager manager = CoreModel.getDefault().getProjectDescriptionManager();
		
		try {
			projDesc = manager.getProjectDescription(project, true);
			if(projDesc == null){
				IProject newProject = CCorePlugin.getDefault().createCProject(project.getDescription(), project, null,project.getName());
				if(newProject != null && newProject.isAccessible()){
					newProject.open(null);
					
					projDesc = CCorePlugin.getDefault().createProjectDescription(newProject, false);	
					
					IManagedBuildInfo info = ManagedBuildManager.createBuildInfo(newProject);					
					IProjectType pt = ManagedBuildManager.getProjectType(DEFAULT_PROJECT_GNU_TYPE);
					IManagedProject proj = ManagedBuildManager.createManagedProject(newProject, pt);
					
					info.setManagedProject(proj);
					buildConfiguration = proj.createConfiguration(ManagedBuildManager.getExtensionConfiguration("cdt.managedbuild.config.gnu.exe.debug"),FEATURE_MAKE_CONFIG_ID);
					buildConfiguration.setName(FEATURE_MAKE_CONFIG_NAME);
					buildConfiguration.setManagedBuildOn(false);
					buildConfiguration.setBuildCommand("make");
					proj.createConfiguration(buildConfiguration, FEATURE_MAKE_CONFIG_ID);
					info.setDefaultConfiguration(buildConfiguration);
					projDesc.createConfiguration(FEATURE_MAKE_CONFIG_ID, buildConfiguration.getConfigurationData());
				}
			}	
			
		} catch (CoreException e1) {
			e1.printStackTrace();
		} catch (BuildException e) {
			e.printStackTrace();
		}
	}

	
	@Override
	public Mechanism getGenerationMechanism() {
		return IComposerExtensionClass.Mechanism.PREPROCESSOR;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.core.builder.ComposerExtensionClass#postModelChanged()
	 */
	@Override
	public void postModelChanged() {
		prepareFullBuild(null);
		annotationChecking();
	}

	private void annotationChecking() {
		deleteAllPreprocessorAnotationMarkers();
		Job job = new Job(PREPROCESSOR_ANNOTATION_CHECKING) {
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				annotationChecking(featureProject.getSourceFolder());
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.SHORT);
		job.schedule();
	}

	private void annotationChecking(IFolder folder) {
		try {
			for (final IResource res : folder.members()) {

				if (res instanceof IFolder) {
					annotationChecking((IFolder) res);
				} else if (res instanceof IFile) {
					final Vector<String> lines = loadStringsFromFile((IFile) res);
					// do checking and some stuff
					processLinesOfFile(lines, (IFile) res);
				}
			}
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	synchronized private void processLinesOfFile(Vector<String> lines, IFile res) {
		expressionStack = new Stack<Node>();

		// count of if, ifelse and else to remove after processing of else from
		// stack
		ifelseCountStack = new Stack<Integer>();

		// go line for line
		for (int j = 0; j < lines.size(); ++j) {
			String line = lines.get(j);

			// if line is preprocessor directive
			if (line.contains("#")) {
				if (line.contains("#if ") || line.contains("#elif ") || line.contains("#ifdef ")
						|| line.contains("#ifndef ") || line.contains("#else")) {

					// remove defined directive to proper work as normal
					// preprocessor.
					line = line.replaceAll("defined", "");

					// if e1, elseif e2, ..., elseif en == if -e1 && -e2 && ...
					// && en
					// if e1, elseif e2, ..., else == if -e1 && -e2 && ...
					if (line.contains("#elif ") || line.contains("#else")) {
						if (!expressionStack.isEmpty()) {
							Node lastElement = new Not(expressionStack.pop().clone());
							expressionStack.push(lastElement);
						}
					} else if (line.contains("#if ") || line.contains("#ifdef ") || line.contains("#ifndef ")) {
						ifelseCountStack.push(0);
					}

					if (!ifelseCountStack.empty() && !line.contains("#else"))
						ifelseCountStack.push(ifelseCountStack.pop() + 1);

					setMarkersContradictionalFeatures(line, res, j + 1);

					setMarkersNotConcreteFeatures(line, res, j + 1);
				} else if (line.contains("#endif")) {
					while (!ifelseCountStack.empty()) {
						if (ifelseCountStack.peek() == 0)
							break;

						if (!expressionStack.isEmpty())
							expressionStack.pop();

						ifelseCountStack.push(ifelseCountStack.pop() - 1);
					}

					if (!ifelseCountStack.empty())
						ifelseCountStack.pop();
				}
			}
		}
	}

	/**
	 * Checks given line if it contains not existing or abstract features.
	 * 
	 * @param line
	 *            content of line
	 * @param res
	 *            file containing given line
	 * @param lineNumber
	 *            line number of given line
	 */
	private void setMarkersNotConcreteFeatures(String line, IFile res, int lineNumber) {
		String[] splitted = line.split(CPPModelBuilder.OPERATORS, 0);

		for (int i = 0; i < splitted.length; ++i) {
			if (!splitted[i].equals("") && !splitted[i].contains("#")) {
				setMarkersOnNotExistingOrAbstractFeature(splitted[i], lineNumber, res);
			}
		}
	}

	/**
	 * Checks given line if it contains expressions which are always
	 * <code>true</code> or <code>false</code>.<br />
	 * <br />
	 * 
	 * Check in three steps:
	 * <ol>
	 * <li>just the given line</li>
	 * <li>the given line and the feature model</li>
	 * <li>the given line, the surrounding lines and the feature model</li>
	 * </ol>
	 * 
	 * @param line
	 *            content of line
	 * @param res
	 *            file containing given line
	 * @param lineNumber
	 *            line number of given line
	 */
	private void setMarkersContradictionalFeatures(String line, IFile res, int lineNumber) {
		if (line.contains("#else")) {
			if (!expressionStack.isEmpty()) {
				Node[] nestedExpressions = new Node[expressionStack.size()];
				nestedExpressions = expressionStack.toArray(nestedExpressions);

				And nestedExpressionsAnd = new And(nestedExpressions);

				isContradictionOrTautology(nestedExpressionsAnd.clone(), true, lineNumber, res);
			}

			return;
		}

		boolean negative = line.contains("#ifndef ");

		// remove "//#if ", "//ifdef", ...
		// TODO TIRAR O defined
		line = replaceCommandPattern.matcher(line).replaceAll("");

		// prepare expression for NodeReader()
		line = line.trim();
		line = line.replace("&&", "&");
		line = line.replace("||", "|");
		line = line.replace("!", "-");
		line = line.replace("&", " and ");
		line = line.replace("|", " or ");
		line = line.replace("-", " not ");

		// get all features and generate Node expression for given line
		Node ppExpression = nodereader.stringToNode(line, featureList);

		if (ppExpression != null) {
			if (negative)
				ppExpression = new Not(ppExpression.clone());

			checkExpressions(ppExpression, lineNumber, res);

		}
	}

	private void createFolder(IFolder folder) throws CoreException {
		if (!folder.exists()) {
			folder.create(true, true, null);
		}
		folder.refreshLocal(IResource.DEPTH_ZERO, null);
	}

	@Override
	public ArrayList<String[]> getTemplates() {
		return TEMPLATES;
	}

	private static final ArrayList<String[]> TEMPLATES = createTempltes();

	private static ArrayList<String[]> createTempltes() {
		ArrayList<String[]> list = new ArrayList<String[]>();
		list.add(new String[] { "C Source File", "c", "\r\n" + "int main(int argc, char **argv)" + " {\r\n\r\n}" });
		list.add(new String[] { C_HEADER_FILE, "h", "#ifndef " + CLASS_NAME_PATTERN + "_H_\n" + "#define "
				+ CLASS_NAME_PATTERN + "_H_\n\n\n" + "#endif /* " + CLASS_NAME_PATTERN + "_H_ */" });
		return list;
	}

	@Override
	public void postCompile(IResourceDelta delta, final IFile file) {

	}

	@Override
	public boolean hasFeatureFolder() {
		return true;
	}

	@Override
	public boolean createFolderForFeatures() {
		return false;
	}

	@Override
	public boolean clean() {
		return false;
	}

	@Override
	public void buildFSTModel() {
		cppModelBuilder.buildModel();
	}

	@Override
	public boolean postAddNature(IFolder source, IFolder destination) {
		return true;
	}

	/**
	 * Show variants with errors
	 */
	private synchronized void verifyVariantsWithProblems() {
//		threadInExecId.remove(Thread.currentThread().getId());
//		if (threadInExecId.isEmpty()) {
//			final Display display = Display.getDefault();
//			if (display == null) {
//				throw new NullPointerException(DISPLAY_IS_NULL);
//			}
//			display.syncExec(new Runnable() {
//				@Override
//				public void run() {
//					InvalidProductsViewController invalidProductViewController = InvalidProductsViewController
//							.getInstance();
//
//					if (!ProjectConfigurationErrorLogger.getInstance().getProjectsList().isEmpty()) {
//						invalidProductViewController.showView();
//
//						List<InvalidProductViewLog> logs = new LinkedList<InvalidProductViewLog>();
//						for (String s : ProjectConfigurationErrorLogger.getInstance().getProjectsList()) {
//							logs.add(new InvalidProductViewLog(s));
//						}
//						invalidProductViewController.setInput(logs);
//					} else {
//						// Clear view
//						// invalidProductViewController.clear();
//						MessageDialog.openInformation(new Shell(), Colligens.PLUGIN_NAME,
//								"The products generated successfully!");
//					}
//
//				}
//
//			});
//
//		}

	}

	@Override
	public void buildConfiguration(IFolder folder, de.ovgu.featureide.fm.core.configuration.Configuration  configuration, String congurationName) {
		super.buildConfiguration(folder, configuration, congurationName);

		createProjectDefinitionsByFeatures(configuration.getSelectedFeatures(),folder.getProjectRelativePath().toOSString()+"/");

	}

	@Override
	public boolean showContextFieldsAndMethods() {
		return true;
	}

	@Override
	public LinkedList<FSTDirective> buildModelDirectivesForFile(Vector<String> lines) {
		return cppModelBuilder.buildModelDirectivesForFile(lines);
	}

	@Override
	public boolean needColor() {
		return true;
	}

	@Override
	public boolean canGeneratInParallelJobs() {
		return true;
	}

}
