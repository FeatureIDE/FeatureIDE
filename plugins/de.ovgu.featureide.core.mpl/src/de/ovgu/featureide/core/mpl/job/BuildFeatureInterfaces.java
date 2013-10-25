package de.ovgu.featureide.core.mpl.job;

import java.util.List;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.io.IOConstants;
import de.ovgu.featureide.core.mpl.signature.ProjectSignatures;
import de.ovgu.featureide.core.mpl.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.mpl.signature.ProjectStructure;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassFragment;
import de.ovgu.featureide.core.mpl.signature.filter.FeatureFilter;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;

public class BuildFeatureInterfaces extends AMonitorJob {
	private final String foldername;
	
	public BuildFeatureInterfaces(String foldername) {
		super("Build Feature Interfaces");
		this.foldername = foldername;
	}
	
	@Override
	protected boolean work() {
		ProjectSignatures projectSignatures = interfaceProject.getProjectSignatures();		
		List<SelectableFeature> features = interfaceProject.getConfiguration().getFeatures();

		IFolder folder = CorePlugin.createFolder(interfaceProject.getProjectReference(), foldername);
		
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
				
				String path = foldername + "/" + feature.getName() + 
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
