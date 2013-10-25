package de.ovgu.featureide.core.mpl.job;

import java.util.LinkedList;

import org.eclipse.core.resources.IFolder;
import org.prop4j.Node;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.io.IOConstants;
import de.ovgu.featureide.core.mpl.signature.ProjectSignatures;
import de.ovgu.featureide.core.mpl.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.mpl.signature.ProjectStructure;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassFragment;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassSignature;
import de.ovgu.featureide.core.mpl.signature.filter.ContextFilter;
import de.ovgu.featureide.fm.core.Feature;

public class BuildExtendedSignatureJob extends AMonitorJob {
	private final String foldername;
	
	public BuildExtendedSignatureJob(String foldername) {
		super("Build Extended Modules");
		this.foldername = foldername;
	}

	@Override
	protected boolean work() {
		IFolder folder = interfaceProject.getProjectReference().getFolder(foldername);
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
		
		sb.append(writeExtendedModule(ps, "_No_Constraints_", foldername));
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
