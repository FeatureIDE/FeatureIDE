/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.core.mpl;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.CompletionProposal;
import org.eclipse.jdt.core.Flags;
import org.eclipse.jdt.core.Signature;
import org.osgi.framework.BundleContext;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.mpl.builder.InterfaceProjectNature;
import de.ovgu.featureide.core.mpl.io.InterfaceWriter;
import de.ovgu.featureide.core.mpl.io.JavaProjectWriter;
import de.ovgu.featureide.core.mpl.io.JavaSignatureWriter;
import de.ovgu.featureide.core.mpl.io.constants.IOConstants;
import de.ovgu.featureide.core.mpl.signature.ProjectSignature;
import de.ovgu.featureide.core.mpl.signature.RoleMap;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassFragment;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractFieldSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractMethodSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature;
import de.ovgu.featureide.core.mpl.util.ConfigurationChangeListener;
import de.ovgu.featureide.core.mpl.util.EditorTracker;
import de.ovgu.featureide.fm.core.AbstractCorePlugin;

/** 
 * Plug-in activator with miscellaneous function for an interface project.
 * 
 * @author Sebastian Krieter
 * @author Reimar Schroeter
 */
public class MPLPlugin extends AbstractCorePlugin {

	public static final String PLUGIN_ID = "de.ovgu.featureide.core.mpl";
	public static boolean WRAPPER_INTERFACES = false;
	public static boolean PRIVATE_METHODS = false;

	private static MPLPlugin plugin;
	private HashMap<String, JavaInterfaceProject> projectMap = new HashMap<String, JavaInterfaceProject>();

	@Override
	public String getID() {
		return PLUGIN_ID;
	}

	public static MPLPlugin getDefault() {
		return plugin;
	}

	@Override
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
		EditorTracker.init(new ConfigurationChangeListener());
	}

	@Override
	public void stop(BundleContext context) throws Exception {
		super.stop(context);
		plugin = null;
		EditorTracker.dispose();
	}
	
	private JavaInterfaceProject addProject(IProject project) {
		JavaInterfaceProject interfaceProject = new JavaInterfaceProject(project);
		projectMap.put(project.getName(), interfaceProject);
		return interfaceProject;
	}
	
	public JavaInterfaceProject getInterfaceProject(String projectName) {
		JavaInterfaceProject interfaceProject = projectMap.get(projectName);
		if (interfaceProject == null) {
			IProject project = ResourcesPlugin.getWorkspace().getRoot().getProject(projectName);
			if (isInterfaceProject(project)) {
				interfaceProject = addProject(project);
			}
		}
		return interfaceProject;
	}
	
	public JavaInterfaceProject getInterfaceProject(IProject project) {
		JavaInterfaceProject interfaceProject = projectMap.get(project.getName());
		if (interfaceProject == null && isInterfaceProject(project)) {
			interfaceProject = addProject(project);
		}
		return interfaceProject;
	}
	
	public boolean isInterfaceProject(IProject project) {
		try {
			return project.getNature(InterfaceProjectNature.NATURE_ID) != null;
		} catch (CoreException e) {
			logError(e);
			return false;
		}
	}
	
	public void setupMultiFeatureProject(Collection<IFeatureProject> featureProjects) {
		for (IFeatureProject featureProject : featureProjects) {
			String projectName = "_" + featureProject.getProjectName() + "_Interfaces";
			
			IProject newProject = ResourcesPlugin.getWorkspace().getRoot().getProject(projectName);
			IProjectDescription description = ResourcesPlugin.getWorkspace().newProjectDescription(projectName);
			description.setNatureIds(new String[]{InterfaceProjectNature.NATURE_ID});
			
			try {
				newProject.create(description, null);
				newProject.open(null);

				//TODO lib ordner mitkopieren und im Java Projekt verlinken
				newProject.getFile(new Path(IOConstants.FILENAME_MODEL)).create(featureProject.getModelFile().getContents(), true, null);

				InputStream stream = new ByteArrayInputStream("".getBytes());
				newProject.getFile(new Path(IOConstants.FILENAME_CONFIG)).create(stream, true, null);
				newProject.getFile(new Path(IOConstants.FILENAME_EXTCONFIG)).create(stream, true, null);
				stream.close();

				JavaInterfaceProject interfaceProject = new JavaInterfaceProject(newProject, featureProject);
				projectMap.put(projectName, interfaceProject);
				
				interfaceProject.getRoleMap().addDefaultViewTag("view1");
				refresh(interfaceProject);
			} catch (Exception e) {
				logError(e);
			}
		}
	}
	
	public void buildFeatureInterfaces(String projectName, String folder, String viewName, int viewLevel, int configLimit) {
		JavaInterfaceProject interfaceProject = getInterfaceProject(projectName);
		if (interfaceProject != null) {
			interfaceProject.refreshRoleMap();
			interfaceProject.setConfigLimit(configLimit);
			interfaceProject.setFilterViewTag(viewName, viewLevel);
			
			if (PRIVATE_METHODS) {
//				refresh(interfaceProject);
				new InterfaceWriter(interfaceProject).buildFeatureInterfaces();
				return;
			}
			
			new InterfaceWriter(interfaceProject).buildFeatureInterfaces(false, folder, true);
		}
	}
	
	public void buildConfigurationInterfaces(String projectName, String viewName, int viewLevel, int configLimit) {
		buildInterfaces(1, projectName, viewName, viewLevel, configLimit);
	}
	
	public void compareConfigurationInterfaces(String projectName, String viewName, int viewLevel, int configLimit) {
		buildInterfaces(0, projectName, viewName, viewLevel, configLimit);
	}
	
	private void buildInterfaces(int mode, String projectName, String viewName, int viewLevel, int configLimit) {
		JavaInterfaceProject interfaceProject = getInterfaceProject(projectName);
		if (interfaceProject != null) {
			interfaceProject.refreshRoleMap();
			interfaceProject.setConfigLimit(configLimit);
			interfaceProject.setFilterViewTag(viewName, viewLevel);
			
			switch (mode) {
			case 0: 
				(new InterfaceWriter(interfaceProject)).compareConfigurationInterfaces();
				break;
			case 1: 
				(new InterfaceWriter(interfaceProject)).buildConfigurationInterfaces();
				break;
			}
		}
	}
	
	public void buildJavaProject(IFile featureListFile, String name) {
		new JavaProjectWriter(getInterfaceProject(featureListFile.getProject())).buildJavaProject(featureListFile, name);
	}
	
	public void addViewTag(IProject project, String name) {
		JavaInterfaceProject interfaceProject = getInterfaceProject(project);
		if (interfaceProject != null) {
			interfaceProject.getRoleMap().addDefaultViewTag(name);
			refresh(interfaceProject);
		}
	}
	
	public void scaleUpViewTag(IProject project, String name, int level) {
		JavaInterfaceProject interfaceProject = getInterfaceProject(project);
		if (interfaceProject != null) {
			interfaceProject.scaleUpViewTag(name, level);
			refresh(interfaceProject);
		}
	}
	
	public void deleteViewTag(IProject project, String name) {
		JavaInterfaceProject interfaceProject = getInterfaceProject(project);
		if (interfaceProject != null) {
			interfaceProject.removeViewTag(name);
			refresh(interfaceProject);
		}
	}
	
	public void refresh(IProject project) {
		JavaInterfaceProject interfaceProject = getInterfaceProject(project);
		if (interfaceProject != null) {
			refresh(interfaceProject);
		}
	}
	
	private void refresh(JavaInterfaceProject interfaceProject) {
		new InterfaceWriter(interfaceProject).buildAllFeatureInterfaces(false);
	}
	

	public void extendedModules(String projectName, String folder) {
		JavaInterfaceProject interfaceProject = getInterfaceProject(projectName);
		if (interfaceProject != null) {
			interfaceProject.refreshRoleMap();
			
			new InterfaceWriter(interfaceProject).createExtendedSignatures(folder);
		}
	}
	
	public void generateStatistics(String projectName, String folder) {
		JavaInterfaceProject interfaceProject = getInterfaceProject(projectName);
		if (interfaceProject != null) {
			interfaceProject.refreshRoleMap();
			
			new InterfaceWriter(interfaceProject).createStatistics(folder);
		}
	}

	public List<CompletionProposal> extendedModules(IFeatureProject project, String featureName) {
		RoleMap map = new JavaSignatureWriter(project, null).writeSignatures(project.getFeatureModel());
		ProjectSignature sig = InterfaceWriter.buildSignature(project.getFeatureModel(), map, featureName);
		Collection<AbstractClassFragment> frag = sig.getClasses();
		
		ArrayList<CompletionProposal> ret_List= new ArrayList<CompletionProposal>();
		for (AbstractClassFragment cur : frag) {
			CompletionProposal pr = org.eclipse.jdt.core.CompletionProposal.create(CompletionProposal.TYPE_REF,0);
			pr.setCompletion(cur.getSignature().getName().toCharArray());
			pr.setFlags(Flags.AccPublic);
			pr.setSignature(Signature.createTypeSignature(cur.getSignature().getFullName(), true).toCharArray());
			ret_List.add(pr);
		}
		
		for (AbstractClassFragment cur : frag) {
			Collection<AbstractSignature> memberFrag = cur.getMembers();
			for (AbstractSignature curMember : memberFrag) {
				if(curMember instanceof AbstractMethodSignature){
					CompletionProposal pr = org.eclipse.jdt.core.CompletionProposal.create(CompletionProposal.METHOD_REF,0);
					
					pr.setDeclarationSignature(Signature.createTypeSignature(cur.getSignature().getFullName(), true).toCharArray());
					pr.setFlags(Flags.AccPublic);
					pr.setName(curMember.getName().toCharArray());
					char[] t = new String("java.lang.String").toCharArray();
//					pr.setSignature(Signature.createMethodSignature(new char[][]{curMember.getName().toCharArray()}, t));
					pr.setSignature(Signature.createMethodSignature(new char[][]{{}}, new char[]{}));
					pr.setCompletion(curMember.getName().toCharArray());
				
					ret_List.add(pr);
				}
				if(curMember instanceof AbstractFieldSignature){
					CompletionProposal pr = org.eclipse.jdt.core.CompletionProposal.create(CompletionProposal.FIELD_REF,0);
					
					pr.setDeclarationSignature(Signature.createTypeSignature(cur.getSignature().getFullName(), true).toCharArray());
					pr.setFlags(Flags.AccPublic);
					pr.setName(curMember.getName().toCharArray());
					pr.setCompletion(curMember.getName().toCharArray());
				
					ret_List.add(pr);
				}
			}
		}
		
		return ret_List;
	}
	
	
	public ProjectSignature extendedModules_getSig(IFeatureProject project, String featureName) {
		RoleMap map = new JavaSignatureWriter(project, null).writeSignatures(project.getFeatureModel());
		ProjectSignature sig = InterfaceWriter.buildSignature(project.getFeatureModel(), map, featureName);
		
		return sig;
	}
	
//	public void extendedModules(IProject project, String folder) {
//		JavaInterfaceProject interfaceProject = getInterfaceProject(project);
//		if (interfaceProject != null) {
//			FeatureModel model = interfaceProject.getFeatureModel();
//			LinkedList<Feature> coreFeatures = model.getAnalyser().getCoreFeatures();
//
//			JavaRoleMap roleMap = interfaceProject.getRoleMap();
////			JavaRoleMap roleMap = new JavaRoleMap(interfaceProject.getRoleMap());
////			JavaFeatureSignature.init(interfaceProject);
//			
//			int rounds = 0;
//			
//			boolean somethingAdded = true;
//			while(somethingAdded){
//				somethingAdded = false;
//				
//				rounds++;
//				
//				//alles von Parent Feature zu den Kindern kopieren....
//				LinkedList<String> listFromRoot = model.getFeatureList();
//				for (String featureName : listFromRoot) {
//					Feature parentFeature = model.getFeature(featureName);
//					JavaFeatureSignature parentSig = roleMap.getRoles(parentFeature.getName());
//					LinkedList<JavaFeatureSignature> childrenSignature = new LinkedList<JavaFeatureSignature>();
//					for (Feature childFeature : parentFeature.getChildren()) {
//						childrenSignature.add(roleMap.getRoles(childFeature.getName()));
//					}
//					
//					if (JavaFeatureSignature.copyFromOnetoX(parentSig, childrenSignature)) {
//						somethingAdded = true;
//					}	
//				}
//				
//				//coreFeatures
//				LinkedList<JavaFeatureSignature> coreFeatureSig = new LinkedList<JavaFeatureSignature>();
//				for (Feature childFeature : coreFeatures) {
//					coreFeatureSig.add(roleMap.getRoles(childFeature.getName()));
//				}
////				LinkedList<JavaFeatureSignature> coreFeatureSig = JavaFeatureSignature.getJavaFeaureSignatureOfFeature(coreFeatures);
//				if (JavaFeatureSignature.unionOfJavaFeatureSignature(coreFeatureSig)) {
//					somethingAdded = true;
//				}
//				
//				//Kinder zu Eltern
//				LinkedList<String> list = model.getFeatureList();
//				while(!list.getLast().equals(model.getRoot().getName())) {
//					String curFeature = list.getLast();
//					Feature parent = model.getFeature(curFeature).getParent();
//					if(parent.isAlternative() || parent.isOr()){
//						JavaFeatureSignature parentFeatureSig = roleMap.getRoles(parent.getName());
//						LinkedList<Feature> curChildren = parent.getChildren();
//						LinkedList<JavaFeatureSignature> sigsOfChilds = getChildFeatureSig(
//								roleMap, list, curChildren);
//						
//						if (JavaFeatureSignature.intersectionOfJavaFeatureSignature(sigsOfChilds, parentFeatureSig)) {
//							somethingAdded = true;
//						}
//					}
//					else if(parent.isAnd()){
//						LinkedList<Feature> children = parent.getChildren();
//						LinkedList<Feature> filteredChildren = new LinkedList<Feature>();
//						for (Feature feature : children) {
//							if(feature.isMandatory() || model.getAnalyser().getFalseOptionalFeatures().contains(feature)){
//								filteredChildren.add(feature);
//							}
//							list.remove(feature.getName());
//						}
//						if(filteredChildren.size() > 0){
//							LinkedList<JavaFeatureSignature> sigsOfChilds = getChildFeatureSig(roleMap, list, filteredChildren);
//						
//							//parent adden... da dieser gleich methoden/felder erhalten muss
//							JavaFeatureSignature featureSig = roleMap.getRoles(parent.getName());
//							sigsOfChilds.add(featureSig);
//							if (JavaFeatureSignature.unionOfJavaFeatureSignature(sigsOfChilds)) {
//								somethingAdded = true;
//							}
//						}
//					} else {
//						list.remove(curFeature);
//					}
//				}
//			}
//			FMCorePlugin.getDefault().logInfo("Rounds: " + rounds);
//				
//			InterfaceWriter interfaceWriter = new InterfaceWriter(interfaceProject);
//			interfaceWriter.buildAllFeatureInterfaces(folder);
//		}		
//	}
//
//	private LinkedList<FeatureRoles> getChildFeatureSig(
//			RoleMap roleMap, LinkedList<String> list,
//			LinkedList<Feature> curChildren) {
//		LinkedList<FeatureRoles> sigsOfChilds = new LinkedList<FeatureRoles>();
//		for (Feature curChild : curChildren) {
//			//Kinder aus der Liste der zu behandelnden Features löschen
//			list.remove(curChild.getName());
//			FeatureRoles featureSig = roleMap.getRoles(curChild.getName());
//			sigsOfChilds.add(featureSig);
//		}
//		return sigsOfChilds;
//	}
}