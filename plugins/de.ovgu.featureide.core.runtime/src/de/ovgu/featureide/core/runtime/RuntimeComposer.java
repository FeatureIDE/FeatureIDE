package de.ovgu.featureide.core.runtime;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.FileSystems;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IJavaElement;
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

	private static class MethodLocation {

		String strClass;
		
		CallLocation[] callLocations;

		public MethodLocation(String strClass, CallLocation[] callLocations) {
			this.callLocations = callLocations;
			this.strClass = strClass;
		}

		public CallLocation[] getCallLocations() {
			return callLocations;
		}

		public String getStrClass() {
			return strClass;
		}

	}

	static final String[] COMPOSITION_MECHANISMS = new String[] { "Run Configuration", "Properties" };

	@Override
	public String[] getCompositionMechanisms() {
		return COMPOSITION_MECHANISMS;
	}

	/**
	 * Every time the project is built, the config will be read and written into
	 * runtime.properties.
	 */
	public static void getCallersOf(IMethod m) {

		// CallHierarchy callHierarchy = CallHierarchy.getDefault();
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

		ArrayList<MethodLocation> callList = new ArrayList<MethodLocation>();

		MethodLocation methodLoc;

		for (int i = 0; i < methodCalls.size(); i++) {

			CallLocation[] callArray = new CallLocation[methodCalls.get(i).getCallLocations().size()];
			methodCalls.get(i).getCallLocations().toArray(callArray);
			methodLoc = new MethodLocation(methodCalls.get(i).getMember().getParent().getElementName(), callArray);
			callList.add(methodLoc);

		}

		for (int i = 0; i < callList.size(); i++) {

			for (int j = 0; j < callList.get(i).getCallLocations().length; j++) {

				System.out.println("Klasse: " + callList.get(i).getStrClass() + " Line: "
						+ callList.get(i).getCallLocations()[j].getLineNumber() + " Calltext: "
						+ callList.get(i).getCallLocations()[j].getCallText());

			}
		}

	}

	@Override
	public void performFullBuild(IFile config) {

		IFile fileProp = featureProject.getProject().getFile("runtime.properties");

		IJavaProject proj = JavaCore.create(featureProject.getProject());

		try {

			IType itype = proj.findType("PropertyManager");
			IMethod method = itype.getMethods()[1];// itype.getMethod("getProperty",
													// new String[] {"String"});

			getCallersOf(method);

		} catch (JavaModelException e1) {
			e1.printStackTrace();
		}

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
	public boolean hasFeatureFolder() {
		return false;
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