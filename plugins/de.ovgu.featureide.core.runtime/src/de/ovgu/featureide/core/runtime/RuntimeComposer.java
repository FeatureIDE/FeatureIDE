package de.ovgu.featureide.core.runtime;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.FileSystems;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Vector;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMember;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.search.IJavaSearchScope;
import org.eclipse.jdt.core.search.SearchEngine;
import org.eclipse.jdt.internal.corext.callhierarchy.CallHierarchy;
import org.eclipse.jdt.internal.corext.callhierarchy.CallLocation;
import org.eclipse.jdt.internal.corext.callhierarchy.MethodCall;
import org.eclipse.jdt.internal.corext.callhierarchy.MethodWrapper;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirectiveCommand;
import de.ovgu.featureide.core.runtime.activator.RuntimeCorePlugin;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.FileReader;

/**
 * 
 * RuntimeComposer creates .property-file from actual configuration or writes
 * arguments from .config file into the program arguments of Eclipse Run
 * Configuration.
 * 
 * @author Kai Wolf
 * @author Matthias Quaas
 *
 */
@SuppressWarnings("restriction")
public class RuntimeComposer extends ComposerExtensionClass {

	public static final String RUN_CONFIGURATION = "Run Configuration";
	public static final String PROPERTIES = "Properties";
	public static final String NOT_EXISTING_PROPERTY_MARKER = CorePlugin.PLUGIN_ID + ".builderProblemMarker";
	public static final String PROPERTY_MANAGER_CLASS = "PropertyManager";
	public static final String PROPERTY_MANAGER_PACKAGE = "properties";
	public static final String GET_PROPERTY_METHOD = "getProperty";
	static final String[] COMPOSITION_MECHANISMS = new String[] { RUN_CONFIGURATION, PROPERTIES };
	static ArrayList<FeatureLocation> featureLocs = new ArrayList<FeatureLocation>();

	@Override
	public String[] getCompositionMechanisms() {
		return COMPOSITION_MECHANISMS;
	}

	@Override
	public boolean hasFeatureFolder() {
		return false;
	}

	@Override
	public boolean needColor() {
		return true;
	}

	@Override
	public boolean hasSourceFolder() {
		return false;
	}

	@Override
	public void postCompile(IResourceDelta delta, IFile buildFile) {
	}

	@Override
	public boolean clean() {
		return false;
	}

	@Override
	public Mechanism getGenerationMechanism() {
		return null;
	}

	@Override
	public LinkedList<FSTDirective> buildModelDirectivesForFile(Vector<String> lines) {
		return new LinkedList<>();
	}

	/**
	 * Every time the project is built, the config will be read and written into
	 * runtime.properties.
	 */
	@Override
	public void performFullBuild(IFile config) {

		IFile fileProp = featureProject.getProject().getFile("runtime.properties");

		if (PROPERTIES.equals(featureProject.getCompositionMechanism())) {

			buildFSTModel();

			final Configuration configuration = readConfig();

			String configString = "";
			for (SelectableFeature f : configuration.getFeatures()) {
				if (!f.getFeature().getStructure().isAbstract()) {
					configString += f.getFeature().getName() + '=' + (f.getSelection() == Selection.SELECTED
							? Boolean.TRUE.toString() : Boolean.FALSE.toString()) + "\n";
				}
			}
			if (configString.contains("\n")) {
				configString = configString.substring(0, configString.lastIndexOf('\n'));
			}
			InputStream inputStream = new ByteArrayInputStream(configString.getBytes(StandardCharsets.UTF_8));

			if (fileProp.exists()) {
				try {
					fileProp.setContents(inputStream, IFile.FORCE, null);
				} catch (CoreException e) {
					RuntimeCorePlugin.getDefault().logError(e);
				}
			} else {
				createFile(fileProp, inputStream);
			}

		} else {
			deleteFile(fileProp);
		}
	}

	/**
	 * Builds FST Model: - adds directives to the model representing each call
	 * of the getProperty()-method - if feature in code does not exist it will
	 * be marked
	 */
	@Override
	public void buildFSTModel() {

		if (PROPERTIES.equals(featureProject.getCompositionMechanism())) {

			// get all current locations of getProperty-calls within the code
			setFeatureLocations();

			// map linking the call location within the code with its directive
			HashMap<FeatureLocation, FSTDirective> directives = new HashMap<FeatureLocation, FSTDirective>();
			FSTModel model = new FSTModel(featureProject);
			int id = 0;
			FSTRole role;

			deleteMarkers();

			for (FeatureLocation loc : featureLocs) {
				if (loc.isInConfig()) {
					// add directive to role and role to model
					model.addRole(loc.getFeatureName(), loc.getClassName(), loc.getClassFile());
					role = model.getRole(loc.getFeatureName(), loc.getClassName());
					FSTDirective fstDirective = setFSTDirective(loc, id);
					fstDirective.setRole(role);
					role.add(fstDirective);
					directives.put(loc, fstDirective);
					id++;
				} else {
					try {
						// marker if feature does not exist in current config
						IMarker newMarker = loc.getClassFile().createMarker(NOT_EXISTING_PROPERTY_MARKER);

						newMarker.setAttribute(IMarker.MESSAGE,
								"Queried Feature '" + loc.getFeatureName() + "' does not exist!");
						newMarker.setAttribute(IMarker.LINE_NUMBER, loc.getStartLineNum());
						newMarker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
					} catch (CoreException e) {
						RuntimeCorePlugin.getDefault().logError(e);
					}
				}
			}
			// set parent-child-relationships
			setDirectiveChilds(directives);

			featureProject.setFSTModel(model);
			super.buildFSTModel();
		}
	}

	/**
	 * Reads and returns current feature config.
	 * 
	 * @return
	 */
	private Configuration readConfig() {

		final Configuration featureProjectConfig = new Configuration(featureProject.getFeatureModel());
		String configPath = featureProject.getCurrentConfiguration().getRawLocation().toOSString();
		FileReader<Configuration> reader = new FileReader<>(configPath, featureProjectConfig,
				ConfigurationManager.getFormat(configPath));
		reader.read();

		return featureProjectConfig;

	}

	/**
	 * Looks for callers of getProperty()-method and creates
	 * FeatureLocation-object for each call.
	 */

	public void setFeatureLocations() {

		featureLocs.clear();
		IJavaProject proj = JavaCore.create(featureProject.getProject());
		try {
			IType itype = proj.findType(PROPERTY_MANAGER_PACKAGE + "." + PROPERTY_MANAGER_CLASS);
			IMethod method = null;

			for (IMethod m : itype.getMethods()) {
				if (m.getElementName().equals(GET_PROPERTY_METHOD)) {
					method = m;
				}
			}
			ArrayList<CallLocation[]> callLocs = getCallersOf(method);

			String featureName;
			String className;
			IFile classFile;
			ICompilationUnit compilationUnit;
			int startLineNum;
			int endLineNum;
			FSTDirectiveCommand cmd;
			for (CallLocation[] callLoc : callLocs) {
				for (int i = 0; i < callLoc.length; i++) {
					// feature name = attribute of getProperty-call
					featureName = callLoc[i].getCallText().split("\"")[1];
					className = callLoc[i].getMember().getParent().getElementName();
					classFile = (IFile) callLoc[i].getMember().getCompilationUnit().getCorrespondingResource();
					compilationUnit = callLoc[i].getMember().getCompilationUnit();
					startLineNum = callLoc[i].getLineNumber();
					endLineNum = getEndOfIf(compilationUnit, startLineNum);
					// if the call in the start line is within an if-statement,
					// getEndOfIf() will return the end of the latter
					cmd = endLineNum == 1 ? FSTDirectiveCommand.CALL : FSTDirectiveCommand.IF;
					endLineNum = endLineNum == 1 ? startLineNum : endLineNum;

					featureLocs
							.add(new FeatureLocation(featureName, startLineNum, endLineNum, classFile, className, cmd));
				}
			}
		} catch (JavaModelException e) {
			RuntimeCorePlugin.getDefault().logError(e);
		}
		// sort all feature locations by 1) class (here represented by path
		// string) and 2) its starting line
		Collections.sort(featureLocs,
				(a, b) -> a.getOSPath().compareTo(b.getOSPath()) == 0
						? (a.getStartLineNum() < b.getStartLineNum() ? -1
								: a.getStartLineNum() == b.getStartLineNum() ? 0 : 1)
						: a.getOSPath().compareTo(b.getOSPath()));

		final Configuration configuration = readConfig();

		// check whether the feature corresponding with the
		// FeatureLocation-object is in the current config
		for (FeatureLocation loc : featureLocs) {
			for (SelectableFeature feature : configuration.getFeatures()) {
				if (feature.getName().equals(loc.getFeatureName())) {
					loc.setInConfig(true);
					break;
				}
			}
		}
		// get parent-child-relations for FeatureLocation-objects
		for (int i = 1; i < featureLocs.size(); i++) {
			FeatureLocation loc = featureLocs.get(i);
			loc.setParent(getParentFeatureLocation(i));
		}
	}

	/**
	 * Method to get all call locations of a method.
	 * 
	 * @param m
	 *            Method for which the call hierarchy will be evaluated.
	 * @return All call locations.
	 */

	private ArrayList<CallLocation[]> getCallersOf(IMethod m) {

		CallHierarchy callHierarchy = new CallHierarchy();
		IJavaSearchScope scope = SearchEngine.createWorkspaceScope();
		callHierarchy.setSearchScope(scope);

		IMember[] members = { m };
		ArrayList<MethodCall> methodCalls = new ArrayList<MethodCall>();

		MethodWrapper[] callerWrapper = callHierarchy.getCallerRoots(members);
		ArrayList<MethodWrapper> callsWrapper = new ArrayList<MethodWrapper>();
		ArrayList<CallLocation[]> callList = new ArrayList<CallLocation[]>();

		for (MethodWrapper mWrapper : callerWrapper) {
			callsWrapper.addAll(Arrays.asList(mWrapper.getCalls(new NullProgressMonitor())));
		}
		for (MethodWrapper mWrapper : callsWrapper) {
			methodCalls.add(mWrapper.getMethodCall());
		}
		for (MethodCall mCall : methodCalls) {
			CallLocation[] callArray = new CallLocation[mCall.getCallLocations().size()];
			mCall.getCallLocations().toArray(callArray);
			callList.add(callArray);
		}

		return callList;

	}

	/**
	 * Gets the end of an if-statement by parsing the class' AST.
	 * 
	 * @param compilationUnit
	 * @param startLineNum
	 *            Indicator for which if statement of the code the end is
	 *            requested.
	 * @return
	 */
	private int getEndOfIf(ICompilationUnit compilationUnit, int startLineNum) {

		ASTParser parser = ASTParser.newParser(AST.JLS8);
		parser.setSource(compilationUnit);
		parser.setKind(ASTParser.K_COMPILATION_UNIT);
		parser.setResolveBindings(true);

		// without this suppress it would throw an error. (strangely not any
		// longer?)
		// @SuppressWarnings("unused")
		ASTNode rootNode = parser.createAST(new NullProgressMonitor());
		IfVisitor astVisitor = new IfVisitor(startLineNum, (CompilationUnit) rootNode);
		rootNode.accept(astVisitor);

		return ((CompilationUnit) rootNode).getLineNumber(astVisitor.getEndPosition());
	}

	/**
	 * Looks for parent-child-relations between FeatureLocation-objects. Its
	 * main aim is to locate nested if-statements.
	 * 
	 * @param startIndex
	 *            Index within {@link featureLocs} indicating the concrete
	 *            object.
	 * @return Parent FeatureLocation-object, null if it has not got a parent.
	 */

	private FeatureLocation getParentFeatureLocation(int startIndex) {
		FeatureLocation startLoc = featureLocs.get(startIndex);
		FeatureLocation prvLoc = null;
		String startClassPath = startLoc.getOSPath();
		String prvClassPath;
		// iterate backwards trough all call locations
		// if the object's starting line is between the previous object's begin
		// and end line it is its child.
		for (int i = startIndex; i >= 1; i--) {
			prvLoc = featureLocs.get(i - 1);
			prvClassPath = prvLoc.getOSPath();

			// do not set the previous location as parent if it is not in the
			// current config
			if (!prvLoc.isInConfig()) {
				prvLoc = null;
				continue;
			}
			// ensure the two FeatureLocation objects are located in the same
			// class
			else if (!startClassPath.equals(prvClassPath)) {
				prvLoc = null;
				break;
			} else if (startLoc.getStartLineNum() > prvLoc.getStartLineNum()
					&& startLoc.getEndLineNum() < prvLoc.getEndLineNum()) {
				break;
			}
			// if the begin is reached but no parent is found prvLoc will be set
			// to null again (after working with it)
			else if ((i - 1) == 0) {
				prvLoc = null;
			}
		}
		return prvLoc;
	}

	/**
	 * Sets the parent-child-relations within the FSTModel by adding children to
	 * parent directives. To determine these relations the
	 * parent-child-relations of the FeatureLocation-objects will be utilized.
	 * 
	 * @param directives
	 *            Map linking FeatureLocation-objects with their FSTDirectives
	 *            representing them in the FSTModel
	 */
	private void setDirectiveChilds(HashMap<FeatureLocation, FSTDirective> directives) {
		FeatureLocation parent = null;
		for (FeatureLocation loc : featureLocs) {
			parent = loc.getParent();
			// only add children to directives when they are in the current
			// config
			if (parent != null && loc.isInConfig()) {
				FSTDirective directiveOfParent = directives.get(parent);
				directiveOfParent.addChild(directives.get(loc));
			}
		}
	}

	private void deleteMarkers() {

		// only delete markers once for each class
		ArrayList<IFile> processedFiles = new ArrayList<IFile>();

		for (FeatureLocation loc : featureLocs) {
			if (!processedFiles.contains(loc.getClassFile())) {
				processedFiles.add(loc.getClassFile());
				try {
					loc.getClassFile().deleteMarkers(NOT_EXISTING_PROPERTY_MARKER, false, IResource.DEPTH_ZERO);
				} catch (CoreException e) {
					RuntimeCorePlugin.getDefault().logError(e);
				}
			}
		}
	}

	/**
	 * Creates the directive which will be added to the FSTModel and set its
	 * properties.
	 * 
	 * @param loc
	 *            FeatureLocation for which the directive needs to be added.
	 * @param id
	 *            Internal id of the new directive
	 * @return Returns created directive.
	 */
	private FSTDirective setFSTDirective(FeatureLocation loc, int id) {

		FSTDirective fstDirective = new FSTDirective();
		fstDirective.setFeatureName(loc.getFeatureName());
		fstDirective.setLine(loc.getStartLineNum());
		fstDirective.setExpression(loc.getFeatureName());
		fstDirective.setStartLine(loc.getStartLineNum() - 1, 0);
		fstDirective.setEndLine(loc.getEndLineNum(), 0);
		fstDirective.setId(id);
		fstDirective.setCommand(loc.getCmd());

		return fstDirective;
	}

	/**
	 * When initialized, the PropertyManager class will be created within the
	 * runtime project, if it does not already exist. The PropertyManager.java
	 * is located in de.ovgu.featureide.core.runtime/resources.
	 */
	@Override
	public boolean initialize(IFeatureProject project) {
		if (super.initialize(project)) {

			IFolder propFolder = featureProject.getBuildFolder().getFolder(PROPERTY_MANAGER_PACKAGE);

			try {
				if (!propFolder.exists()) {
					propFolder.create(true, true, new NullProgressMonitor());
				}
			} catch (CoreException e) {
				RuntimeCorePlugin.getDefault().logError(e);
			}
			IFile filePropMan = propFolder.getFile(PROPERTY_MANAGER_CLASS + ".java");

			if (PROPERTIES.equals(featureProject.getCompositionMechanism())) {
				if (!filePropMan.exists()) {
					InputStream inputStream = null;
					try {
						inputStream = FileLocator.openStream(
								RuntimeCorePlugin.getDefault().getBundle(), new Path("Resources"
										+ FileSystems.getDefault().getSeparator() + PROPERTY_MANAGER_CLASS + ".java"),
								false);
					} catch (IOException e) {
						RuntimeCorePlugin.getDefault().logError(e);
					}
					createFile(filePropMan, inputStream);
					try {
						filePropMan.setDerived(true, null);
					} catch (CoreException e) {
						RuntimeCorePlugin.getDefault().logError(e);
					}
				}
			} else {
				deleteFile(filePropMan);
				try {
					propFolder.delete(true, null);
				} catch (CoreException e) {
					RuntimeCorePlugin.getDefault().logError(e);
				}
			}
		}
		return super.initialize(project);
	}

	private void deleteFile(IFile file) {
		if (file != null) {
			try {
				file.delete(true, null);
			} catch (CoreException e) {
				RuntimeCorePlugin.getDefault().logError(e);
			}
		}
	}

	private void createFile(IFile file, InputStream stream) {
		if (file != null) {
			try {
				file.create(stream, true, null);
			} catch (CoreException e) {
				RuntimeCorePlugin.getDefault().logError(e);
			}
		}
	}

}