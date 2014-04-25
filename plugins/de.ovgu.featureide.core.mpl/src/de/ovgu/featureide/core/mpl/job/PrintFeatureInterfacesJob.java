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
package de.ovgu.featureide.core.mpl.job;

import java.util.List;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.io.IOConstants;
import de.ovgu.featureide.core.mpl.job.util.AMonitorJob;
import de.ovgu.featureide.core.mpl.job.util.AJobArguments;
import de.ovgu.featureide.core.mpl.signature.ProjectSignatures;
import de.ovgu.featureide.core.mpl.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.mpl.signature.ProjectStructure;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassFragment;
import de.ovgu.featureide.core.mpl.signature.filter.FeatureFilter;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;

/**
 * Builds interfaces for a single feature.
 * 
 * @author Sebastian Krieter
 */
public class PrintFeatureInterfacesJob extends AMonitorJob<PrintFeatureInterfacesJob.Arguments> {
	
	public static class Arguments extends AJobArguments {
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
		ProjectSignatures projectSignatures = interfaceProject.getProjectSignatures();		
		List<SelectableFeature> features = interfaceProject.getConfiguration().getFeatures();

		IFolder folder = CorePlugin.createFolder(interfaceProject.getProjectReference(), arguments.foldername);
		
		try {
			folder.delete(true, null);
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}

		setMaxAbsoluteWork(features.size());
		int[] curFeature = new int[1];
		SignatureIterator it = interfaceProject.getProjectSignatures().createIterator();
		
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
			worked();
		}
		IOConstants.writeToFile(interfaceProject.getProjectReference().getFile("SPL_Statistic.txt"), 
				projectSignatures.getStatisticsString());
		MPLPlugin.getDefault().logInfo("Built Feature Interfaces");
		
		return true;
	}
}
