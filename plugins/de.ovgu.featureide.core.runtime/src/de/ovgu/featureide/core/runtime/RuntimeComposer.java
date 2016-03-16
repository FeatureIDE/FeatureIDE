package de.ovgu.featureide.core.runtime;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.FileSystems;
import java.util.ArrayList;
import java.util.Arrays;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMember;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.search.IJavaSearchScope;
import org.eclipse.jdt.core.search.SearchEngine;
import org.eclipse.jdt.internal.corext.callhierarchy.CallHierarchy;
import org.eclipse.jdt.internal.corext.callhierarchy.CallLocation;
import org.eclipse.jdt.internal.corext.callhierarchy.MethodCall;
import org.eclipse.jdt.internal.corext.callhierarchy.MethodWrapper;

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

	static final String[] COMPOSITION_MECHANISMS = new String[] { "Run Configuration", "Properties" };

	@Override
	public String[] getCompositionMechanisms() {
		return COMPOSITION_MECHANISMS;
	}

	/**
	 * Method to get all call locations of a method.
	 * @param m Method for which the call hierarchy will be evaluated.
	 * @return All call locations.
	 */
	private static ArrayList<CallLocation[]> getCallersOf(IMethod m) {

		CallHierarchy callHierarchy = new CallHierarchy();
		IJavaSearchScope scope = SearchEngine.createWorkspaceScope();
		callHierarchy.setSearchScope(scope);

		IMember[] members = {m};
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
	@Override
	public void performFullBuild(IFile config) {

		IFile fileProp = featureProject.getProject().getFile("runtime.properties");

		if (COMPOSITION_MECHANISMS[1].equals(featureProject.getCompositionMechanism())) {

			String configPath = config.getRawLocation().toOSString();
			final Configuration configuration = new Configuration(featureProject.getFeatureModel());
			FileReader<Configuration> reader = new FileReader<>(configPath, configuration,
					ConfigurationManager.getFormat(configPath));
			reader.read();

			String configString = "";
			for (SelectableFeature f : configuration.getFeatures()) {
				if (!f.getFeature().getStructure().isAbstract()) {
					configString += f.getFeature().getName() + '=' + (f.getSelection() == Selection.SELECTED
							? Boolean.TRUE.toString() : Boolean.FALSE.toString()) + "\n";
				}
			}

			configString = configString.substring(0, configString.lastIndexOf('\n'));
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
		IJavaProject proj = JavaCore.create(featureProject.getProject());

		FSTModel model = new FSTModel(featureProject);

		try {
			IType itype = proj.findType("PropertyManager");
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
			FSTRole role;
			int lineNumber;

			for (CallLocation[] callLoc : callLocs) {
				for (int i = 0; i < callLoc.length; i++) {
					featureName = callLoc[i].getCallText().split("\"")[1];
					className = callLoc[i].getMember().getParent().getElementName();
					classFile = (IFile) callLoc[i].getMember().getCompilationUnit().getCorrespondingResource();
					lineNumber = callLoc[i].getLineNumber();

					model.addRole(featureName, className, classFile);
					role = model.getRole(featureName, className);

					setFSTDirective(featureName, className, lineNumber, role/*, alreadyUsedNames*/);
					
				}
			}
		} catch (JavaModelException e) {
			RuntimeCorePlugin.getDefault().logError(e);
		}
		featureProject.setFSTModel(model);
		
		super.buildFSTModel();
	}
	/**
	 * Sets the directives which will be added to the FSTModel.
	 * @param featureName
	 * @param className
	 * @param lineNumber
	 * @param role
	 */
	private void setFSTDirective(String featureName, String className, int lineNumber, FSTRole role) {

		FSTDirective fstDirective = new FSTDirective();
		fstDirective.setCommand(FSTDirectiveCommand.IF);
		fstDirective.setFeatureName(featureName);
		fstDirective.setLine(lineNumber);
		fstDirective.setRole(role);
		fstDirective.setExpression(featureName);
		fstDirective.setStartLine(lineNumber - 1, 0);
		fstDirective.setEndLine(lineNumber+2, 0);

		role.add(fstDirective);

	}

	@Override
	public boolean hasFeatureFolder() {
		return false;
	}
	@Override
	public boolean needColor() {
		return true;
	};

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
			IFile filePropMan = featureProject.getBuildFolder().getFile(propertyManager);

			if (COMPOSITION_MECHANISMS[1].equals(featureProject.getCompositionMechanism())) {
				InputStream inputStream = null;
				try {
					inputStream = FileLocator.openStream(RuntimeCorePlugin.getDefault().getBundle(),
							new Path("Resources" + FileSystems.getDefault().getSeparator() + propertyManager), false);
				} catch (IOException e) {
					RuntimeCorePlugin.getDefault().logError(e);
				}
				if (!filePropMan.exists()) {
					createFile(filePropMan, inputStream);
					try {
						filePropMan.setDerived(true, null);
					} catch (CoreException e) {
						RuntimeCorePlugin.getDefault().logError(e);
					}
				}
			} else {
				deleteFile(filePropMan);
			}
		}
		return super.initialize(project);
	}

	@Override
	public Mechanism getGenerationMechanism() {
		return null;
	}
}