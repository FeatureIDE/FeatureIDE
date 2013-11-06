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

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
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

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.FeatureProjectNature;
import de.ovgu.featureide.core.mpl.builder.InterfaceProjectNature;
import de.ovgu.featureide.core.mpl.io.IOConstants;
import de.ovgu.featureide.core.mpl.io.writer.JavaProjectWriter;
import de.ovgu.featureide.core.mpl.job.AChainJob;
import de.ovgu.featureide.core.mpl.job.BuildExtendedSignatureJob;
import de.ovgu.featureide.core.mpl.job.BuildFeatureInterfaces;
import de.ovgu.featureide.core.mpl.job.BuildStatisticsJob;
import de.ovgu.featureide.core.mpl.job.CompareConfigInterfaces;
import de.ovgu.featureide.core.mpl.job.StartJob;
import de.ovgu.featureide.core.mpl.signature.ProjectSignatures;
import de.ovgu.featureide.core.mpl.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.mpl.signature.ProjectStructure;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractFieldSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractMethodSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature;
import de.ovgu.featureide.core.mpl.signature.filter.ContextFilter;
import de.ovgu.featureide.core.mpl.util.ConfigurationChangeListener;
import de.ovgu.featureide.core.mpl.util.EditorTracker;
import de.ovgu.featureide.fm.core.AbstractCorePlugin;
import de.ovgu.featureide.fm.core.PropertyConstants;

/** 
 * Plug-in activator with miscellaneous function for an interface project.
 * 
 * @author Sebastian Krieter
 * @author Reimar Schroeter
 */
public class MPLPlugin extends AbstractCorePlugin {
	public static final String PLUGIN_ID = "de.ovgu.featureide.core.mpl";

	private static MPLPlugin plugin;
	private final HashMap<String, InterfaceProject> projectMap = new HashMap<String, InterfaceProject>();

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
	
	public void addInterfaceNature(IProject project) {
		IFeatureProject curFeatureProject = CorePlugin.getFeatureProject(project);
		// TODO MPL: workaround: only for feature house projects
		if (curFeatureProject != null
				&& "de.ovgu.featureide.composer.featurehouse"
						.equals(curFeatureProject.getComposerID())) {
			try {
				IProjectDescription description = project.getDescription();
				String[] natures = description.getNatureIds();
				String[] newNatures = new String[natures.length + 1];
				System.arraycopy(natures, 0, newNatures, 0, natures.length);
				newNatures[natures.length] = InterfaceProjectNature.NATURE_ID;
				description.setNatureIds(newNatures);
				project.setDescription(description, null);
			} catch (CoreException e) {
				logError(e);
			}
		}
	}
	
	public void removeInterfaceNature(IProject project) {
		try {
			IProjectDescription description = project.getDescription();
			String[] natures = description.getNatureIds();
			String[] newNatures = new String[natures.length - 1];
			int i = 0;
			for (String nature : natures) {
				if (!nature.equals(InterfaceProjectNature.NATURE_ID)) {
					newNatures[i++] = nature;
				}
			}
			description.setNatureIds(newNatures);
			project.setDescription(description, null);
		} catch (CoreException e) {
			logError(e);
		}
	}
	
	private InterfaceProject addProject(IProject project) {
		IFeatureProject curFeatureProject = null;
		try {
			if (project.hasNature(FeatureProjectNature.NATURE_ID)) {
				curFeatureProject = CorePlugin.getFeatureProject(project);
			} else {
				for (IFeatureProject fp : CorePlugin.getFeatureProjects()) {
					if (constructInterfaceProjectName(fp.getProjectName()).equals(project.getName())) {
						curFeatureProject = fp;
						break;
					}
				}
			}
		} catch (CoreException e) {
			logError(e);
		}
		final InterfaceProject interfaceProject = new InterfaceProject(project, curFeatureProject);
		
		projectMap.put(project.getName(), interfaceProject);
		interfaceProject.getFeatureModel().addListener(new PropertyChangeListener() {
			@Override
			public void propertyChange(PropertyChangeEvent evt) {
				if (PropertyConstants.MODEL_DATA_CHANGED.equals(evt.getPropertyName())) {
//					interfaceProject.loadSignatures(true);
				} else if (PropertyConstants.MODEL_LAYOUT_CHANGED.equals(evt.getPropertyName())) {
//					interfaceProject.loadSignatures(true);
				}
			}
		});
		return interfaceProject;
	}
	
	public InterfaceProject getInterfaceProject(String projectName) {
		InterfaceProject interfaceProject = projectMap.get(projectName);
		if (interfaceProject == null) {
			IProject project = ResourcesPlugin.getWorkspace().getRoot().getProject(projectName);
			if (isInterfaceProject(project)) {
				interfaceProject = addProject(project);
			}
		}
		return interfaceProject;
	}
	
	public InterfaceProject getInterfaceProject(IProject project) {
		InterfaceProject interfaceProject = projectMap.get(project.getName());
		if (interfaceProject == null && isInterfaceProject(project)) {
			interfaceProject = addProject(project);
		}
		return interfaceProject;
	}
	
	public boolean isInterfaceProject(IProject project) {
		try {
			return project.hasNature(InterfaceProjectNature.NATURE_ID);
		} catch (CoreException e) {
			logError(e);
			return false;
		}
	}
	
	private static String constructInterfaceProjectName(String featureProjektName) {
		return "_" + featureProjektName + "_Interfaces";
	}
	
	public void setupMultiFeatureProject(Collection<IFeatureProject> featureProjects) {
		for (IFeatureProject featureProject : featureProjects) {			
			String projectName = constructInterfaceProjectName(featureProject.getProjectName());
			
			IProject newProject = ResourcesPlugin.getWorkspace().getRoot().getProject(projectName);
			IProjectDescription description = ResourcesPlugin.getWorkspace().newProjectDescription(projectName);
			description.setNatureIds(new String[]{InterfaceProjectNature.NATURE_ID});			
			try {
				newProject.create(description, null);
				newProject.open(null);
				
				newProject.getFile(new Path(IOConstants.FILENAME_MODEL)).create(featureProject.getModelFile().getContents(), true, null);

				InputStream stream = new ByteArrayInputStream("".getBytes());
				newProject.getFile(new Path(IOConstants.FILENAME_CONFIG)).create(stream, true, null);
				newProject.getFile(new Path(IOConstants.FILENAME_EXTCONFIG)).create(stream, true, null);
				stream.close();

				InterfaceProject interfaceProject = new InterfaceProject(newProject, featureProject);
				projectMap.put(projectName, interfaceProject);
			} catch (Exception e) {
				logError(e);
			}
		}
	}
	
	public void buildJavaProject(IFile featureListFile, String name) {
		new JavaProjectWriter(getInterfaceProject(featureListFile.getProject())).buildJavaProject(featureListFile, name);
	}
	
	public void addViewTag(IProject project, String name) {
		InterfaceProject interfaceProject = getInterfaceProject(project);
		if (interfaceProject != null) {
//			interfaceProject.getRoleMap().addDefaultViewTag(name);
//			refresh(interfaceProject);
		}
	}
	
	public void scaleUpViewTag(IProject project, String name, int level) {
		InterfaceProject interfaceProject = getInterfaceProject(project);
		if (interfaceProject != null) {
//			interfaceProject.scaleUpViewTag(name, level);
//			refresh(interfaceProject);
		}
	}
	
	public void deleteViewTag(IProject project, String name) {
		InterfaceProject interfaceProject = getInterfaceProject(project);
		if (interfaceProject != null) {
//			interfaceProject.removeViewTag(name);
//			refresh(interfaceProject);
		}
	}
	
	public void refresh(IProject project) {
		InterfaceProject interfaceProject = getInterfaceProject(project);
		if (interfaceProject != null) {
			interfaceProject.loadSignatures(true);
//			interfaceProject.loadSignaturesJob(true);
		}
	}
	
	public void buildFeatureInterfaces(LinkedList<IProject> projects, String folder, String viewName, int viewLevel, int configLimit) {
		final AChainJob[] jobs = new AChainJob[projects.size()];
		for (int i = 0; i < jobs.length; i++) {
			jobs[i] = new BuildFeatureInterfaces(folder);
		}
		startJobs(projects, jobs);
	}
	
	public void buildConfigurationInterfaces(LinkedList<IProject> projects, String viewName, int viewLevel, int configLimit) {
		final AChainJob[] jobs = new AChainJob[projects.size()];
		for (int i = 0; i < jobs.length; i++) {
			jobs[i] = new CompareConfigInterfaces();
		}
		startJobs(projects, jobs);
	}
	
	public void compareConfigurationInterfaces(LinkedList<IProject> projects, String viewName, int viewLevel, int configLimit) {
		final AChainJob[] jobs = new AChainJob[projects.size()];
		for (int i = 0; i < jobs.length; i++) {
			jobs[i] = new CompareConfigInterfaces();
		}
		startJobs(projects, jobs);
	}
	
//	public void extendedModules(String projectName, String folder) {
//		addJob(projectName, new BuildExtendedSignatureJob(folder));
//	}
	
	public void buildExtendedModules(LinkedList<IProject> projects, String folder) {
		final AChainJob[] jobs = new AChainJob[projects.size()];
		for (int i = 0; i < jobs.length; i++) {
			jobs[i] = new BuildExtendedSignatureJob(folder);
		}
		startJobs(projects, jobs);
	}
	
	public void printStatistics(LinkedList<IProject> projects, String folder) {
		final AChainJob[] jobs = new AChainJob[projects.size()];
		for (int i = 0; i < jobs.length; i++) {
			jobs[i] = new BuildStatisticsJob(folder);
		}
		startJobs(projects, jobs);
	}
	
//	private void addJob(String projectName, AChainJob job) {
//		InterfaceProject interfaceProject = getInterfaceProject(projectName);
//		if (interfaceProject != null) {			
//			interfaceProject.loadSignaturesJob(false);
//			job.setInterfaceProject(interfaceProject);
//			interfaceProject.addJob(job);
//		}
//	}
	
	private void startJobs(LinkedList<IProject> projects, AChainJob[] jobs) {
		final InterfaceProject[] interfaceProjects = new InterfaceProject[projects.size()];
		int i = 0;
		for (IProject p : projects) {
			InterfaceProject interfaceProject = getInterfaceProject(p.getName());
			if (interfaceProject != null) {
				interfaceProjects[i] = interfaceProject;
				jobs[i++].setInterfaceProject(interfaceProject);
			}
		}
		StartJob startJob = new StartJob(jobs);
		startJob.schedule();
	}
	
	//TODO MPL: use Fuji
	public List<CompletionProposal> extendedModules_getCompl(IFeatureProject project, String featureName) {
		final LinkedList<CompletionProposal> ret_List = new LinkedList<CompletionProposal>();
		
		InterfaceProject interfaceProject = getInterfaceProject(project.getProject());
		if (interfaceProject != null) {	
			final ProjectSignatures signatures = interfaceProject.getProjectSignatures();
			if (signatures != null) {
				SignatureIterator it = signatures.createIterator();
				it.addFilter(new ContextFilter(featureName, interfaceProject));
//				Iterator<AbstractSignature> it = signatures.getIterator(new ContextFilter(featureName, interfaceProject));
				
				while (it.hasNext()) {
					AbstractSignature curMember = it.next();
					CompletionProposal pr = null;
					
					if (curMember instanceof AbstractMethodSignature) {
						pr = CompletionProposal.create(CompletionProposal.METHOD_REF, 0);
						pr.setSignature(Signature.createMethodSignature(new char[][]{{}}, new char[]{}));
					} else if (curMember instanceof AbstractFieldSignature) {
						pr = CompletionProposal.create(CompletionProposal.FIELD_REF, 0);
//						pr.setDeclarationSignature(Signature.createTypeSignature(cur.getSignature().getFullName(), true).toCharArray());
					} else if (curMember instanceof AbstractClassSignature) {
						pr = CompletionProposal.create(CompletionProposal.TYPE_REF,0);
						pr.setSignature(Signature.createTypeSignature(curMember.getFullName(), true).toCharArray());
					}
					
					if (pr != null) {
//						pr2.setDeclarationSignature(Signature.createTypeSignature(cur.getSignature().getFullName(), true).toCharArray());
						pr.setFlags(Flags.AccPublic);
						pr.setName(curMember.getName().toCharArray());
						pr.setCompletion(curMember.getName().toCharArray());
						
						ret_List.add(pr);
					}
				}
			} else {
				interfaceProject.loadSignatures(false);
			}
		}
		return ret_List;
	}

	public ProjectStructure extendedModules_getStruct(final IFeatureProject project, final String featureName) {
		InterfaceProject interfaceProject = getInterfaceProject(project.getProject());
		if (interfaceProject != null) {	
			final ProjectSignatures signatures = interfaceProject.getProjectSignatures();
			if (signatures != null) {
				SignatureIterator it = signatures.createIterator();
				it.addFilter(new ContextFilter(featureName, interfaceProject));
				return new ProjectStructure(it);
			} else {
				interfaceProject.loadSignatures(false);
			}
		}
		return null;
	}
}