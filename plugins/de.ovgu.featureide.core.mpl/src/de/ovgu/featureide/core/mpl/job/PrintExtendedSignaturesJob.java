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

import java.util.LinkedList;

import org.eclipse.core.resources.IFolder;
import org.prop4j.Node;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.io.IOConstants;
import de.ovgu.featureide.core.mpl.job.util.AMonitorJob;
import de.ovgu.featureide.core.mpl.job.util.AJobArguments;
import de.ovgu.featureide.core.mpl.signature.ProjectSignatures;
import de.ovgu.featureide.core.mpl.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.mpl.signature.ProjectStructure;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassFragment;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassSignature;
import de.ovgu.featureide.core.mpl.signature.filter.ContextFilter;
import de.ovgu.featureide.fm.core.Feature;

/**
 * Builds extended signatures for different constraints.
 * 
 * @author Sebastian Krieter
 */
public class PrintExtendedSignaturesJob extends AMonitorJob<PrintExtendedSignaturesJob.Arguments> {
	
	public static class Arguments extends AJobArguments {
		private final String foldername;
		
		public Arguments(String foldername) {
			super(Arguments.class);
			this.foldername = foldername;
		}
	}
	
	protected PrintExtendedSignaturesJob(Arguments arguments) {
		super("Build Extended Modules", arguments);
	}

	@Override
	protected boolean work() {
		IFolder folder = interfaceProject.getProjectReference().getFolder(arguments.foldername);
		IOConstants.clearFolder(folder);
		
		LinkedList<String> allConcreteFeatures = new LinkedList<String>();
		for (Feature feature : interfaceProject.getFeatureModel().getConcreteFeatures()) {
			if (!feature.isHidden()) {
				allConcreteFeatures.add(feature.getName());
			}
		}
		setMaxAbsoluteWork(allConcreteFeatures.size() + 1);
		
		StringBuilder sb = new StringBuilder();
		sb.append("_No_Constraints_\n");

		ProjectSignatures p = interfaceProject.getProjectSignatures();
		SignatureIterator it = p.createIterator();
		
		ContextFilter filter = new ContextFilter(new Node[]{}, interfaceProject);
		it.addFilter(filter);
		
		ProjectStructure ps = new ProjectStructure(it);
		
		sb.append(writeExtendedModule(ps, "_No_Constraints_", arguments.foldername));
		worked();
		
		for (String featureName : allConcreteFeatures) {
			sb.append("\n");
			sb.append(featureName);
			sb.append("\n\n");
			filter.init(featureName);
			ps = new ProjectStructure(it);
//			sb.append(writeExtendedModule(ps, featureName, foldername));
			worked();
		}
		
		IOConstants.writeToFile(folder.getFile("all_statistics.txt"), sb.toString());
		
		MPLPlugin.getDefault().logInfo("Built Extended Modules");
		return true;
	}
	
	private String writeExtendedModule(ProjectStructure signature, String featureName, String folderName) {
		for (AbstractClassFragment curClass : signature.getClasses()) {
			AbstractClassSignature classSig = curClass.getSignature();
			final String packagename = classSig.getPackage();
			final String path = folderName + "/" + featureName + (packagename.isEmpty() ? "" :"/" + packagename);
			
			IFolder folder = CorePlugin.createFolder(interfaceProject.getProjectReference(), path);
			
			IOConstants.writeToFile(folder.getFile(classSig.getName() + IOConstants.EXTENSION_JAVA), curClass.toShortString());
		}
		
		IFolder folder = CorePlugin.createFolder(interfaceProject.getProjectReference(), folderName + "/" + featureName);		
		IOConstants.writeToFile(folder.getFile("statistics.txt"), signature.getStatisticsString());
		return signature.getStatisticsStringHeader();
	}
}
