/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.featurehouse.refactoring.pullUp;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.ltk.core.refactoring.CheckConditionsOperation;
import org.eclipse.ltk.core.refactoring.PerformRefactoringOperation;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.Features;

/**
 * TODO description
 * 
 * @author steffen
 */
public class AutomaticPullUpMember {

	private final PullUpRefactoring refactoring;
	public AutomaticPullUpMember(AbstractClassSignature classSignature, IFeatureProject project, String file)
	{
		refactoring = new PullUpRefactoring(classSignature, project, file);
	}
	
	public void setUp(){
//		final IWorkspace workspace = ResourcesPlugin.getWorkspace();
//		final String path = workspace.getRoot().getLocation().toOSString();
//		final IProjectDescription desc = workspace.loadProjectDescription(new Path(path + "/HelloWorld-FH-Java-Test/.project"));
//		final IProject project = workspace.getRoot().getProject(desc.getName());
//		if (!project.exists()) project.create(null);
//		if (!project.isOpen())  project.open(null);
//		CorePlugin.getDefault().addProject(project);
//		featureProject = CorePlugin.getFeatureProjects().iterator().next();
//		
//		IOverwriteQuery overwriteQuery = new IOverwriteQuery() {
//	        public String queryOverwrite(String file) { return ALL; }
//		};
//		
//		project.refreshLocal(IResource.DEPTH_INFINITE, new NullProgressMonitor());
//
//		String baseDir = path + "/HelloWorld-FH-Java-Test";// location of files to import""
//				
//		ImportOperation importOperation = new ImportOperation(project.getFullPath(),
//		        new File(baseDir), FileSystemStructureProvider.INSTANCE, overwriteQuery);
//		importOperation.setCreateContainerStructure(false);
//		importOperation.run(new NullProgressMonitor());
//		
//		project.refreshLocal(IResource.DEPTH_INFINITE, new NullProgressMonitor());
//		
//		ExtendedFujiSignaturesJob efsj = new ExtendedFujiSignaturesJob(featureProject);
//		efsj.schedule();
//		efsj.join();
//		
//		signatures = featureProject.getFSTModel().getProjectSignatures();
	}
	
	public void pullUpAllClonedMembers() {
		
		final Map<AbstractSignature, List<Feature>> clonedSignatures = refactoring.getClonedSignatures();

		final Set<ExtendedPullUpSignature> pullUpMembers = new HashSet<>();
		final Set<ExtendedPullUpSignature> deletableMembers = new HashSet<>();

		final Feature destinationFeature = determineDestinationFeature(clonedSignatures);
		if (destinationFeature == null) return;
		int featureId;
		for (Entry<AbstractSignature, List<Feature>> entry : clonedSignatures.entrySet()) {
			
			featureId = refactoring.getProjectSignatures().getFeatureID(refactoring.getSourceFeature().getName());
			pullUpMembers.add(new ExtendedPullUpSignature(entry.getKey(), featureId));
			
			for (Feature feature : entry.getValue()) {
				featureId = refactoring.getProjectSignatures().getFeatureID(feature.getName());
				deletableMembers.add(new ExtendedPullUpSignature(entry.getKey(), featureId));
			}
		}
		
		refactoring.setDestinationFeature(destinationFeature);
		refactoring.setPullUpSignatures(pullUpMembers);
		refactoring.setDeletableSignatures(deletableMembers);
		
		IProgressMonitor monitor = new NullProgressMonitor();
			
		PerformRefactoringOperation op = new PerformRefactoringOperation(refactoring, CheckConditionsOperation.ALL_CONDITIONS);
		try {
			op.run(monitor);
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}

	private Feature determineDestinationFeature(Map<AbstractSignature, List<Feature>> clonedSignatures) {
		Set<Feature> allFeatures = new HashSet<>();
		
		for (List<Feature> features : clonedSignatures.values()) {
			allFeatures.addAll(features);
		} 
		
		final List<Feature> commonAncestors = Features.getCommonAncestors(allFeatures);
		if (commonAncestors == null || commonAncestors.size() == 0) return null;
		
		commonAncestors.remove(refactoring.getSourceFeature());
		return commonAncestors.get(commonAncestors.size() -1);
	}
}
