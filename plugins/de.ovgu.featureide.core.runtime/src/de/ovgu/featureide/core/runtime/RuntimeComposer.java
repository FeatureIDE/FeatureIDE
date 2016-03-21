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
import java.util.List;
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
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.IfStatement;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.MethodRef;
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
 * @author Matthias Quaas
 * @author Kai Wolf
 *
 */
@SuppressWarnings("restriction")
public class RuntimeComposer extends ComposerExtensionClass {

	public static final String RUN_CONFIGURATION = "Run Configuration";
	public static final String PROPERTIES = "Properties";
	private final String NOT_EXISTING_PROPERTY_MARKER = CorePlugin.PLUGIN_ID + ".builderProblemMarker";
	static final String[] COMPOSITION_MECHANISMS = new String[] { RUN_CONFIGURATION, PROPERTIES };
	static ArrayList<FeatureLocation> featureLocs = new ArrayList<FeatureLocation>();

	class FeatureLocation {

		String featureName;
		int startLineNum;
		IFile classFile;
		String className;
		int endLineNum;
		FeatureLocation parent;
		boolean inConfig;
		FSTDirectiveCommand cmd;

		FeatureLocation(String featureName, int lineNumber, int endLineNum, IFile classFile, String className,
				FSTDirectiveCommand cmd) {
			this.featureName = featureName;
			this.startLineNum = lineNumber;
			this.classFile = classFile;
			this.className = className;
			this.endLineNum = endLineNum;
			this.parent = null;
			this.inConfig = false;
			this.cmd = cmd;
		}

		public FSTDirectiveCommand getCmd() {
			return cmd;
		}

		public String getFeatureName() {
			return featureName;
		}

		public int getStartLineNum() {
			return startLineNum;
		}

		public IFile getClassFile() {
			return classFile;
		}

		public String getClassName() {
			return className;
		}

		public int getEndLineNum() {
			return endLineNum;
		}

		public FeatureLocation getParent() {
			return parent;
		}

		public boolean isInConfig() {
			return inConfig;
		}

		public void setFeatureName(String featureName) {
			this.featureName = featureName;
		}

		public void setParent(FeatureLocation parent) {
			this.parent = parent;
		}

		public void setInConfig(boolean existsInConfig) {
			this.inConfig = existsInConfig;
		}

		public void setCmd(FSTDirectiveCommand cmd) {
			this.cmd = cmd;
		}

		public String toString() {
			return classFile.getFullPath().toOSString() + "_" + startLineNum + "_" + featureName;
		}

	}

	@Override
	public String[] getCompositionMechanisms() {
		return COMPOSITION_MECHANISMS;
	}

	/**
	 * Method to get all call locations of a method.
	 * 
	 * @param m
	 *            Method for which the call hierarchy will be evaluated.
	 * @return All call locations.
	 */
	private static ArrayList<CallLocation[]> getCallersOf(IMethod m) {

		CallHierarchy callHierarchy = new CallHierarchy();
		IJavaSearchScope scope = SearchEngine.createWorkspaceScope();
		callHierarchy.setSearchScope(scope);

		IMember[] members = { m };
		ArrayList<MethodCall> methodCalls = new ArrayList<MethodCall>();

		MethodWrapper[] callerWrapper = callHierarchy.getCallerRoots(members);
		ArrayList<MethodWrapper> callsWrapper = new ArrayList<MethodWrapper>();
		for (int i = 0; i < callerWrapper.length; i++) {
			callsWrapper.addAll(Arrays.asList(callerWrapper[i].getCalls(new NullProgressMonitor())));
		}

		for (int i = 0; i < callsWrapper.size(); i++) {
			methodCalls.add(callsWrapper.get(i).getMethodCall());
		}

		ArrayList<CallLocation[]> callList = new ArrayList<CallLocation[]>();
		for (int i = 0; i < methodCalls.size(); i++) {
			CallLocation[] callArray = new CallLocation[methodCalls.get(i).getCallLocations().size()];
			methodCalls.get(i).getCallLocations().toArray(callArray);
			callList.add(callArray);
		}
		return callList;

	}

	/**
	 * Every time the project is built, the config will be read and written into
	 * runtime.properties.
	 */

	private Configuration readConfig() {

		final Configuration featureProjectConfig = new Configuration(featureProject.getFeatureModel());
		String configPath = featureProject.getCurrentConfiguration().getRawLocation().toOSString();
		FileReader<Configuration> reader = new FileReader<>(configPath, featureProjectConfig,
				ConfigurationManager.getFormat(configPath));
		reader.read();

		return featureProjectConfig;

	}

	@Override
	public void performFullBuild(IFile config) {

		IFile fileProp = featureProject.getProject().getFile("runtime.properties");

		if (COMPOSITION_MECHANISMS[1].equals(featureProject.getCompositionMechanism())) {

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

	@Override
	public void buildFSTModel() {

		if (COMPOSITION_MECHANISMS[1].equals(featureProject.getCompositionMechanism())) {

			final Configuration configuration = readConfig();

			setFeatureLocations();

			HashMap<FeatureLocation, FSTDirective> directives = new HashMap<FeatureLocation, FSTDirective>();
			FSTModel model = new FSTModel(featureProject);
			int id = 0;
			FSTRole role;
			int endLineNum;

			deleteMarkers();

			for (FeatureLocation loc : featureLocs) {

				for (SelectableFeature feature : configuration.getFeatures()) {
					if (feature.getName().equals(loc.getFeatureName())) {
						loc.setInConfig(true);
						break;
					}
				}
				if (loc.isInConfig()) {
					model.addRole(loc.getFeatureName(), loc.getClassName(), loc.getClassFile());
					role = model.getRole(loc.getFeatureName(), loc.getClassName());
					directives.put(loc, setFSTDirective(loc, role, id));
					id++;
				} else {

					try {
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

			setChilds(directives);
			// FSTDirective[] bla = new
			// FSTDirective[directives.values().size()];
			// directives.values().toArray(bla);

			featureProject.setFSTModel(model);
			super.buildFSTModel();
		}
	}

	private void setChilds(HashMap<FeatureLocation, FSTDirective> directives) {
		FeatureLocation parent = null;
		for (FeatureLocation loc : featureLocs) {
			parent = loc.getParent();
			if (parent != null && loc.isInConfig()) {
				FSTDirective directiveOfParent = directives.get(parent);
				directiveOfParent.addChild(directives.get(loc));
			}
		}

	}

	private void deleteMarkers() {
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
	 * Sets the directives which will be added to the FSTModel.
	 * 
	 * @param featureName
	 * @param className
	 * @param startLineNum
	 * @param role
	 * @param id
	 * @return
	 */
	private FSTDirective setFSTDirective(FeatureLocation loc, FSTRole role, int id) {

		FSTDirective fstDirective = new FSTDirective();
		fstDirective.setFeatureName(loc.getFeatureName());
		fstDirective.setLine(loc.getStartLineNum());
		fstDirective.setRole(role);
		fstDirective.setExpression(loc.getFeatureName());
		fstDirective.setStartLine(loc.getStartLineNum() - 1, 0);
		fstDirective.setEndLine(loc.getEndLineNum(), 0);
		fstDirective.setId(id);
		fstDirective.setCommand(loc.getCmd());
		

		role.add(fstDirective);

		return fstDirective;
	}

	public void setFeatureLocations() {

		featureLocs.clear();
		IJavaProject proj = JavaCore.create(featureProject.getProject());

		try {
			IType itype = proj.findType("properties.PropertyManager");
			IMethod method = null;

			for (IMethod m : itype.getMethods()) {
				if (m.getElementName().equals("getProperty")) {
					method = m;
				}
			}

			ArrayList<CallLocation[]> callLocs = getCallersOf(method);

			String featureName;
			String className;
			IFile classFile;
			int startLineNum;
			int endLineNum;

			for (CallLocation[] callLoc : callLocs) {
				for (int i = 0; i < callLoc.length; i++) {
					featureName = callLoc[i].getCallText().split("\"")[1];
					className = callLoc[i].getMember().getParent().getElementName();
					classFile = (IFile) callLoc[i].getMember().getCompilationUnit().getCorrespondingResource();
					ICompilationUnit compilationUnit = callLoc[i].getMember().getCompilationUnit();
					startLineNum = callLoc[i].getLineNumber();
					endLineNum = getEndOfIf(compilationUnit, startLineNum);

					FSTDirectiveCommand cmd = endLineNum == 1 ? FSTDirectiveCommand.CALL : FSTDirectiveCommand.IF;
					endLineNum = endLineNum == 1 ? startLineNum : endLineNum;

					featureLocs
							.add(new FeatureLocation(featureName, startLineNum, endLineNum, classFile, className, cmd));

					// int endLineNum = ((CompilationUnit)
					// rootNode).getLineNumber(astVisitor.getEndPosition());
					// System.out.println("Start: " + startLineNum + " Name: " +
					// featureName);
					// System.out.println("Ende: " + endLineNum);
				}
			}
		} catch (JavaModelException e) {
			RuntimeCorePlugin.getDefault().logError(e);
		}
		// Collections.sort(featureLocs,
		// (a, b) ->
		// a.classFile.getFullPath().toOSString().compareTo(b.classFile.getFullPath().toOSString()));
		// Collections.sort(featureLocs,
		// (a, b) -> a.startLineNum < b.startLineNum ? -1 : a.startLineNum ==
		// b.startLineNum ? 0 : 1);
		Collections.sort(featureLocs, (a, b) -> a.toString().compareTo(b.toString()));
		for (int i = 1; i < featureLocs.size(); i++) {
			FeatureLocation loc = featureLocs.get(i);
			loc.setParent(getParent(i));
		}
		for (FeatureLocation f : featureLocs) {
			System.out.println("Klasse: " + f.getClassName());
			System.out.println("Feature: " + f.getFeatureName());
			System.out.println("Start: " + f.getStartLineNum());
			System.out.println("Ende: " + f.getEndLineNum());
			if (f.getParent() == null)
				System.out.println("kein Parent");
			else {
				System.out.println("Parent Start: " + f.getParent().getStartLineNum());
			}
		}

	}

	private FeatureLocation getParent(int startIndex) {
		String startClassPath = featureLocs.get(startIndex).getClassFile().getFullPath().toOSString();
		String prvClassPath = featureLocs.get(startIndex - 1).getClassFile().getFullPath().toOSString();
		FeatureLocation startLoc = featureLocs.get(startIndex);
		FeatureLocation prvLoc = featureLocs.get(startIndex - 1);
		if (startLoc.getStartLineNum() == 27) {
			System.out.println("nhi");
		}
		for (int i = startIndex; i >= 1; i--) {
			// startLoc = featureLocs.get(i);
			prvLoc = featureLocs.get(i - 1);
			prvClassPath = prvLoc.getClassFile().getFullPath().toOSString();
			if (!startClassPath.equals(prvClassPath)) {
				prvLoc = null;
				break;
			} else if (startLoc.getStartLineNum() > prvLoc.getStartLineNum()
					&& startLoc.getEndLineNum() < prvLoc.getEndLineNum()) {
				break;
			} else if ((i - 1) == 0) {
				prvLoc = null;
			}
		}
		return prvLoc;
	}

	private int getEndOfIf(ICompilationUnit compilationUnit, int startLineNum) {

		ASTParser parser = ASTParser.newParser(AST.JLS8);
		parser.setSource(compilationUnit);
		parser.setKind(ASTParser.K_COMPILATION_UNIT);
		parser.setResolveBindings(true);

		@SuppressWarnings("unused")
		ASTNode rootNode = parser.createAST(new NullProgressMonitor());
		IfVisitor astVisitor = new IfVisitor(startLineNum, (CompilationUnit) rootNode);
		rootNode.accept(astVisitor);

		return ((CompilationUnit) rootNode).getLineNumber(astVisitor.getEndPosition())
				;
	}

	class IfVisitor extends ASTVisitor {

		int endPosition;
		int startLine;
//		int elseLength;
		// int parentStartLine;
		CompilationUnit compilationUnit;

		public IfVisitor(int startLine, CompilationUnit compilationUnit) {
			super();
			endPosition = 0;
//			elseLength = 0;
			this.startLine = startLine;
			this.compilationUnit = compilationUnit;
		}

		public void endVisit(IfStatement node) {

			if (compilationUnit.getLineNumber(node.getStartPosition()) == startLine) {
//				endPosition = node.getStartPosition();
				endPosition = node.getThenStatement().getStartPosition();
				// elseLength= node.getElseStatement() == null? 0 :
				// node.getElseStatement().getLength()-1;
				// System.out.println("else "+elseLength);
				endPosition += node.getThenStatement().getLength();
				// parentStartLine =
				// compilationUnit.getLineNumber(node.getParent().getStartPosition());
			}

			// System.out.println("Aktuelle Zeile: " +
			// compilationUnit.getLineNumber(node.getStartPosition()));
			// System.out.println("Parentline: " +
			// compilationUnit.getLineNumber(node.getParent().getStartPosition()));

			super.endVisit(node);

		}

		public void endVisit(MethodRef node) {
			System.out.println("Aktuelle Zeile Method: " + compilationUnit.getLineNumber(node.getStartPosition()));
			System.out.println(
					"Parentline Method: " + compilationUnit.getLineNumber(node.getParent().getStartPosition()));
			super.endVisit(node);
		}

		public void endVisit(MethodInvocation node) {
			// if (node.getName().toString().equals("getProperty")) {
			/*
			 * System.out.println("Methodenname: " + node.getName());
			 * System.out.println("Aktuelle Zeile Method: " +
			 * compilationUnit.getLineNumber(node.getStartPosition()));
			 * System.out.println( "Parentline Method: " +
			 * compilationUnit.getLineNumber(node.getParent().getStartPosition()
			 * ));
			 */
			// }
			// parentStartLine=
			// compilationUnit.getLineNumber(node.getParent().getStartPosition());
			super.endVisit(node);

		}

		/*
		 * public boolean visit(IfStatement unit) { if (offset == 0) { offset =
		 * unit.getStartPosition(); offset += unit.getLength(); } return
		 * super.visit(unit); }
		 */

		public int getEndPosition() {
			return endPosition;

		}

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

	private static void deleteFile(IFile file) {
		if (file != null) {
			try {
				file.delete(true, null);
			} catch (CoreException e) {
				RuntimeCorePlugin.getDefault().logError(e);
			}
		}
	}

	private static void createFile(IFile file, InputStream stream) {
		if (file != null) {
			try {
				file.create(stream, true, null);
			} catch (CoreException e) {
				RuntimeCorePlugin.getDefault().logError(e);
			}
		}
	}

	/**
	 * When initialized, the PropertyManager class will be created within the
	 * runtime project, if it does not exists already. The PropertyManager.java
	 * is located in de.ovgu.featureide.core.runtime/resources.
	 */
	@Override
	public boolean initialize(IFeatureProject project) {
		if (super.initialize(project)) {
			final String propertyManager = "PropertyManager.java";
			final String propertyPackage = "properties";
			IFolder propFolder = featureProject.getBuildFolder().getFolder(propertyPackage);

			try {
				if (!propFolder.exists()) {
					propFolder.create(true, true, new NullProgressMonitor());
				}
			} catch (CoreException e) {
				System.out.println("hi");
				RuntimeCorePlugin.getDefault().logError(e);
			}
			IFile filePropMan = propFolder.getFile(propertyManager);

			if (COMPOSITION_MECHANISMS[1].equals(featureProject.getCompositionMechanism())) {
				if (!filePropMan.exists()) {
					InputStream inputStream = null;
					try {
						inputStream = FileLocator.openStream(RuntimeCorePlugin.getDefault().getBundle(),
								new Path("Resources" + FileSystems.getDefault().getSeparator() + propertyManager),
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

	@Override
	public Mechanism getGenerationMechanism() {
		return null;
	}

	@Override
	public LinkedList<FSTDirective> buildModelDirectivesForFile(Vector<String> lines) {
		return new LinkedList<>();
	}

}