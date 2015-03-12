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
package de.ovgu.featureide.core.mpl.job;

import java.util.List;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.mpl.InterfaceProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.ProjectStructure;
import de.ovgu.featureide.core.signature.base.AbstractClassFragment;
import de.ovgu.featureide.core.signature.filter.FeatureFilter;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.io.IOConstants;
import de.ovgu.featureide.fm.core.job.AProjectJob;
import de.ovgu.featureide.fm.core.job.util.JobArguments;

/**
 * Builds interfaces for a single feature.
 * 
 * @author Sebastian Krieter
 */
public class PrintFeatureInterfacesJob extends AProjectJob<PrintFeatureInterfacesJob.Arguments> {
	
	public static class Arguments extends JobArguments {
		private final String foldername;
		
		public Arguments(String foldername) {
			super(Arguments.class);
			this.foldername = foldername;
		}
	}
	
	protected PrintFeatureInterfacesJob(Arguments arguments) {
		super("Build Feature Interfaces", arguments);
	}
	
	@Override
	protected boolean work() {
		InterfaceProject interfaceProject = MPLPlugin.getDefault().getInterfaceProject(this.project);
		if (interfaceProject == null) {
			MPLPlugin.getDefault().logWarning(this.project.getName() + " is no Interface Project!");
			return false;
		}
		ProjectSignatures projectSignatures = interfaceProject.getProjectSignatures();		
		List<SelectableFeature> features = interfaceProject.getConfiguration().getFeatures();

		IFolder folder = CorePlugin.createFolder(interfaceProject.getProjectReference(), arguments.foldername);
		
		try {
			folder.delete(true, null);
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}

		workMonitor.setMaxAbsoluteWork(features.size());
		int[] curFeature = new int[1];
		SignatureIterator it = interfaceProject.getProjectSignatures().iterator();
		
		for (SelectableFeature feature : features) {
			curFeature[0] = interfaceProject.getFeatureID(feature.getName());
			it.clearFilter();
			it.addFilter(new FeatureFilter(curFeature));
			
			ProjectStructure structure = new ProjectStructure(it);
			for (AbstractClassFragment role : structure.getClasses()) {
				String packagename = role.getSignature().getPackage();
				
				String path = arguments.foldername + "/" + feature.getName() + 
					(packagename.isEmpty() ? "" :"/" + packagename);
				
				folder = CorePlugin.createFolder(interfaceProject.getProjectReference(), path);
				IOConstants.writeToFile(
						folder.getFile(role.getSignature().getName() + IOConstants.EXTENSION_JAVA),
						role.toShortString());
			}
			workMonitor.worked();
		}
		IOConstants.writeToFile(interfaceProject.getProjectReference().getFile("SPL_Statistic.txt"), 
				projectSignatures.getStatisticsString());
		MPLPlugin.getDefault().logInfo("Built Feature Interfaces");
		
		return true;
	}
}
