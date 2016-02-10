package de.ovgu.featureide.featuremake;

import static de.ovgu.featureide.fm.core.localization.StringTable.C_HEADER_FILE;
import static de.ovgu.featureide.fm.core.localization.StringTable.DISPLAY_IS_NULL;
import static de.ovgu.featureide.fm.core.localization.StringTable.IS_NOT_INSTALLED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.PREPROCESSOR_ANNOTATION_CHECKING;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_REQUIRED_BUNDLE;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.Stack;
import java.util.Vector;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;
import org.prop4j.And;
import org.prop4j.Node;
import org.prop4j.Not;

import br.ufal.ic.colligens.activator.Colligens;
import br.ufal.ic.colligens.controllers.core.CPPModelBuilder;
import br.ufal.ic.colligens.controllers.core.CPPWrapper;
import br.ufal.ic.colligens.controllers.invalidproducts.InvalidProductsViewController;
import br.ufal.ic.colligens.util.InvalidProductViewLog;
import br.ufal.ic.colligens.util.ProjectConfigurationErrorLogger;
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
	// public static final String CC_NATURE = "org.eclipse.cdt.core.ccnature";

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
		return false;
	}

	@Override
	public boolean initialize(IFeatureProject project) {
		boolean supSuccess = super.initialize(project);
		cppModelBuilder = new CPPModelBuilder(project);

		// Start typeChef
		// Setup the controller
		// typeChef = new TypeChef();
		prepareFullBuild(null);
		annotationChecking();

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
			String[] natures = description.getNatureIds();
			String[] newNatures = new String[natures.length + 1];
			System.arraycopy(natures, 0, newNatures, 0, natures.length);
			newNatures[natures.length] = C_NATURE;
			description.setNatureIds(newNatures);
			project.setDescription(description, null);

		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}

	}

	@Override
	public void performFullBuild(IFile config) {

		IFeatureModel model = CorePlugin.getFeatureProject(config).getFeatureModel();
		Configuration cfg = new Configuration(model);
		final FileReader<Configuration> reader = new FileReader<>(Paths.get(config.getLocationURI()), cfg,
				ConfigurationManager.getFormat(config.getName()));
		reader.read();
		
		List<String> args = new ArrayList<String>();
		args.add("make");
		args.add("-B");
		StringBuilder sb = new StringBuilder();
		sb.append("USERDEFS=");
		for (SelectableFeature sbf : cfg.getFeatures()) {
			IFeature feature = sbf.getFeature();
			IFeatureStructure structure = feature.getStructure();
			
			if (sbf.getSelection() == Selection.SELECTED && structure.isConcrete()) {
				sb.append("-D").append(sbf.getName()).append(" ");
			}
		}
		String sourceDirectory = Paths.get(this.featureProject.getProject().getLocationURI()) + "/source/";
		args.add(sb.toString());
		args.add("-C" + sourceDirectory);
		args.add("-fMakefile");
		ProcessBuilder processBuilder = new ProcessBuilder(args);
		processBuilder.redirectErrorStream(true);
		try {
			final Process process = processBuilder.start();
			new Thread() {
				@Override
				public void run() {
					BufferedReader input = new BufferedReader(new InputStreamReader(process.getInputStream()));
					  String line = null;
					 MessageConsole console = findConsole("Console");
					 MessageConsoleStream out = console.newMessageStream();		            
					 try {
				   		while ((line = input.readLine()) != null) {
				  		         out.println(line);
					   	 }
					} catch (IOException e) {
						e.printStackTrace();
					}
				}
			}.start();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		/*
		 * if (!isPluginInstalled(PLUGIN_CDT_ID)) {
		 * generateWarning(PLUGIN_WARNING); }
		 * 
		 * if (!prepareFullBuild(config)) return; // // // Job job = new
		 * Job("Analyzing!") { // @Override // protected IStatus
		 * run(IProgressMonitor monitor) { // //this perfom a build using the
		 * Feature configuration selected // IFolder buildFolder =
		 * featureProject.getBuildFolder(); // // if
		 * (buildFolder.getName().equals("src")) { // buildFolder = //
		 * featureProject.getProject().getFolder(System.getProperty(
		 * "file.separator") // + // "build"); // } //
		 * runTypeChefAnalyzes(featureProject.getSourceFolder()); // //
		 * if(continueCompilationFlag){ // runBuild(getActivatedFeatureArgs(),
		 * featureProject.getSourceFolder(), // buildFolder); // } // return
		 * Status.OK_STATUS; // } // }; // job.setPriority(Job.SHORT); //
		 * job.schedule(); // // // // if (cppModelBuilder != null) {
		 * cppModelBuilder.buildModel(); } annotationChecking();
		 */
	}
	
	private MessageConsole findConsole(String name){
		ConsolePlugin plugin = ConsolePlugin.getDefault();
		IConsoleManager conMan = plugin.getConsoleManager();
		IConsole[] existing = conMan.getConsoles();
		for (int i = 0; i < existing.length; i++)
			if (name.equals(existing[i].getName()))
				return (MessageConsole) existing[i];
		
		//no console found, so create a new one
		MessageConsole myConsole = new MessageConsole(name, null);
		conMan.addConsoles(new IConsole[]{myConsole});
		return myConsole;
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
			Colligens.getDefault().logError(e);
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

	/**
	 * Prepare the directives to C PreProcessor adding -D arg for each feature
	 * 
	 * @param myActivatedFeatures
	 *            list of all activated features for one build
	 * @return list in the form -D FEATUREA -D FEATUREB -D FEATUREC
	 */
	private LinkedList<String> getActivatedFeatureArgs(List<String> myActivatedFeatures) {
		LinkedList<String> args = new LinkedList<String>();
		for (String feature : myActivatedFeatures) {
			args.add("-D" + feature);
		}
		return args;

	}

	/**
	 * In this method, all files in a given source folder are preprocessed by
	 * CPP
	 * 
	 * @param featureArgs
	 *            arguments to CPP preprocessor and compiler
	 * @param fileList
	 *            list of all files found in folders and subfolders
	 * @param sourceFolder
	 *            the origin of files
	 * @param buildFolder
	 *            the destination of the compilation/preprocessment
	 * @param cpp
	 *            that contains methods that compile/preprocess C files
	 * @throws CoreException
	 */
	@SuppressWarnings("unchecked")
	private void prepareFilesConfiguration(LinkedList<String> featureArgs, List<String> fileList, IFolder sourceFolder,
			IFolder buildFolder, CPPWrapper cpp) throws CoreException {

		String fullFilePath = null;
		List<String> preProcessorInput;
		String preProcessorOutput;
		for (final IResource res : sourceFolder.members()) {
			if (res instanceof IFolder) {
				buildFolder = featureProject.getProject()
						.getFolder(buildFolder.getProjectRelativePath() + File.separator + res.getName());
				createFolder(buildFolder);
				prepareFilesConfiguration(featureArgs, fileList, (IFolder) res, buildFolder, cpp);
			} else if (res instanceof IFile) {
				if (!res.getFileExtension().equals("c") && !res.getFileExtension().equals("h")) {
					continue;
				}
				String[] name = res.getName().split("\\.");
				fullFilePath = res.getLocation().toOSString();
				fileList.add(fullFilePath);
				preProcessorInput = (LinkedList<String>) featureArgs.clone();
				preProcessorInput.add(fullFilePath);
				preProcessorOutput = buildFolder.getLocation().toOSString() + System.getProperty("file.separator")
						+ name[0] + "_preprocessed." + res.getFileExtension();

				// CommandLine syntax:
				// -DFEATURE1 -DFEATURE2 ... File1 outputDirectory/File1
				cpp.runPreProcessor(preProcessorInput, preProcessorOutput);
			}

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
		return false;
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
		System.out.println("akkkkkkk"); // TODO: remove
		threadInExecId.remove(Thread.currentThread().getId());
		if (threadInExecId.isEmpty()) {
			final Display display = Display.getDefault();
			if (display == null) {
				throw new NullPointerException(DISPLAY_IS_NULL);
			}
			display.syncExec(new Runnable() {
				@Override
				public void run() {
					InvalidProductsViewController invalidProductViewController = InvalidProductsViewController
							.getInstance();

					if (!ProjectConfigurationErrorLogger.getInstance().getProjectsList().isEmpty()) {
						invalidProductViewController.showView();

						List<InvalidProductViewLog> logs = new LinkedList<InvalidProductViewLog>();
						for (String s : ProjectConfigurationErrorLogger.getInstance().getProjectsList()) {
							logs.add(new InvalidProductViewLog(s));
						}
						invalidProductViewController.setInput(logs);
					} else {
						// Clear view
						// invalidProductViewController.clear();
						MessageDialog.openInformation(new Shell(), Colligens.PLUGIN_NAME,
								"The products generated successfully!");
					}

				}

			});

		}

	}

	@Override
	public void buildConfiguration(IFolder folder, Configuration configuration, String congurationName) {
		super.buildConfiguration(folder, configuration, congurationName);

		List<String> myActivatedFeatures = new LinkedList<String>();

		for (IFeature feature : configuration.getSelectedFeatures()) {
			myActivatedFeatures.add(feature.getName());
		}

		// runBuild(getActivatedFeatureArgs(myActivatedFeatures),
		// featureProject.getSourceFolder(), folder);

		// displays the products with errors
		verifyVariantsWithProblems();

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
