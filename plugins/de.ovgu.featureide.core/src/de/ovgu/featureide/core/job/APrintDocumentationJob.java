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
package de.ovgu.featureide.core.job;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.ProjectStructure;
import de.ovgu.featureide.core.signature.base.AbstractClassFragment;
import de.ovgu.featureide.core.signature.documentation.ContextMerger;
import de.ovgu.featureide.core.signature.documentation.FeatureModuleMerger;
import de.ovgu.featureide.core.signature.documentation.SPLMerger;
import de.ovgu.featureide.core.signature.documentation.VariantMerger;
import de.ovgu.featureide.core.signature.documentation.base.ADocumentationCommentMerger;
import de.ovgu.featureide.core.signature.filter.FOPContextFilter;
import de.ovgu.featureide.core.signature.filter.FeatureFilter;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationReader;
import de.ovgu.featureide.fm.core.io.IOConstants;
import de.ovgu.featureide.fm.core.job.AProjectJob;
import de.ovgu.featureide.fm.core.job.util.JobArguments;

/**
 * This job generates Javadoc from the feature-aware comments in a selected location.
 * Subsequently it uses the Javadoc parser to generate the documentation.
 * 
 * @author Sebastian Krieter
 */
public abstract class APrintDocumentationJob extends AProjectJob<APrintDocumentationJob.Arguments> {
	
	public static class Arguments extends JobArguments {
		private final String foldername, featurename;
		private final int mode; 
		private final String[] options;
		
		public Arguments(String foldername, String featurename, int mode, String[] options) {
			super(Arguments.class);
			this.foldername = foldername;
			this.featurename = featurename;
			this.mode = mode;
			this.options = options;
		}
	}
	
	protected APrintDocumentationJob(Arguments arguments) {
		super("Build Documentation", arguments);
	}

	@Override
	protected boolean work() {		
		final IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
		if (featureProject == null) {
			CorePlugin.getDefault().logWarning(this.project.getName() + " is no FeatureIDE Project!");
		}
		
		if (!deleteOldFolder()) {
			return false;
		}
		
		final ProjectSignatures projectSignatures = featureProject.getProjectSignatures();
		if (projectSignatures == null) {
			CorePlugin.getDefault().logWarning("No signatures available!");
		}
		
		final SignatureIterator it = projectSignatures.iterator();
		
//		FeatureNames names = new FeatureNames(featureProject.getFeatureModel());		
		int[] featureIDs = new int[projectSignatures.getFeatureCount()];
		int i = 0;
		for (String string : projectSignatures.getFeatureModel().getFeatureOrderList()) {
			featureIDs[i++] = projectSignatures.getFeatureID(string);
		}
		int index = -1;
		if (arguments.featurename != null) {
			index = projectSignatures.getFeatureID(arguments.featurename);
		}
		
		ADocumentationCommentMerger merger = null;
		switch (arguments.mode) {
		// ----------------------------------- SPL ---------------------------------------------
		case 0: 
			merger = new SPLMerger();
			break;
			
		// -------------------------------- Variante ---------------------------------------------
		case 1:
			final Configuration conf = new Configuration(featureProject.getFeatureModel(),
					Configuration.PARAM_LAZY | Configuration.PARAM_IGNOREABSTRACT);
			try {
				IFile file = featureProject.getCurrentConfiguration();
				new ConfigurationReader(conf).readFromFile(file);
			} catch (Exception e) {
				CorePlugin.getDefault().logError(e);
				return false;
			}
			final List<Feature> featureSet = conf.getSelectedFeatures();
			
			final int[] tempFeatureList = new int[featureSet.size()];
			int count = 0;
			for (Feature selctedFeature : featureSet) {
				final int id = projectSignatures.getFeatureID(selctedFeature.getName());
				if (id >= 0) {
					tempFeatureList[count++] = id;
				}
			}
			final int[] featureList = new int[count];
			
			// sort feature list
			int c = 0;
			for (int j = 0; j < featureIDs.length; j++) {
				int curId = featureIDs[j];
				for (int k = 0; k < count; k++) {
					if (curId == tempFeatureList[k]) {
						featureList[c++] = curId;
						break;
					}
				}
			}
			
			it.addFilter(new FeatureFilter(featureList));
			System.out.println();
			merger = new VariantMerger(featureIDs.length, featureList);
			break;
//			
//		// --------------------------------- Context ---------------------------------------------
		case 2:
			if (index > -1) {
				it.addFilter(new FOPContextFilter(arguments.featurename, projectSignatures));
				merger = new ContextMerger(featureIDs.length, featureIDs);
			}
			break;
//			
//		// ------------------------------- Featuremodul ------------------------------------------
		case 3:
			if (index > -1) {
//				int[] shortFeatureIDs = null;
//				for (int j = 0; j < featureIDs.length; j++) {
//					if (index == featureIDs[j]) {
//						shortFeatureIDs = new int[j + 1];
//						System.arraycopy(featureIDs, 0, shortFeatureIDs, 0, j + 1);
//						break;
//					}
//				}
//				if (shortFeatureIDs == null) {
//					//warning?
//					return false;
//				}
				
//				it.addFilter(new ContextFilter(arguments.featurename, interfaceProject));
//				it.addFilter(new FeatureFilter(shortFeatureIDs));
				it.addFilter(new FeatureFilter(new int[]{index}));
				merger = new FeatureModuleMerger(featureIDs.length, index);
			}
			break;
			
		default:
			return false;
		}
		
		if (merger == null) {
			return false;
		}
		
//		while (it.hasNext()) {
//			merger.setSig(it.next());
//			merger.mergeComments();
//		}
//		it.reset();

		buildJavaDoc(it);
		return true;
	}
	
	protected String folderPath = null;
	
	private boolean deleteOldFolder() {
		final IFolder folder = CorePlugin.createFolder(this.project, arguments.foldername);
		folderPath = folder.getLocation().toOSString();
		
		try {
			folder.delete(true, null);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
			return false;
		}
		return true;
	}

	private void buildJavaDoc(final SignatureIterator it) {
		final String extFoldername = arguments.foldername + "/src/";
		
		CorePlugin.createFolder(this.project, extFoldername);
		
		final HashSet<String> packageSet = new HashSet<String>();
		final LinkedList<String> classList = new LinkedList<String>();
		final ProjectStructure structure = new ProjectStructure(it);
		final String docOutput = folderPath + "\\doc\\";
		final String srcOutput = folderPath + "\\src\\";
		
		workMonitor.setMaxAbsoluteWork(structure.getClasses().size() + 2);
		
		for (AbstractClassFragment javaClass : structure.getClasses()) {
			String packagename = javaClass.getSignature().getPackage();
			
			String path = extFoldername + packagename.replace('.', '/');
			
			if (packagename.isEmpty()) {
				classList.add(srcOutput + javaClass.getSignature().getName() + IOConstants.EXTENSION_JAVA);
			} else {
				packageSet.add(packagename);
			}
			
			final IFolder folder = CorePlugin.createFolder(project, path);
			IOConstants.writeToFile(
					folder.getFile(javaClass.getSignature().getName() + IOConstants.EXTENSION_JAVA),
					javaClass.toString());
			workMonitor.worked();
		}
		final IFolder folder = CorePlugin.createFolder(project, arguments.foldername + "/doc/");
		
		final int defaultArguments = 4;
		int numDefaultArguments = defaultArguments;
		String[] args0 = null, args1 = null;
		
		if (!classList.isEmpty()) {
			args0 = new String[classList.size()];
			classList.toArray(args0);
			numDefaultArguments += args0.length;
		}
		if (!packageSet.isEmpty()) {
			if (args0 == null) {
				args0 = new String[packageSet.size()];
				packageSet.toArray(args0);
			} else {
				args1 = new String[packageSet.size()];
				packageSet.toArray(args1);
			}
			numDefaultArguments += packageSet.size();
		}
		
		final String[] javadocargs;
		if (arguments.options != null && arguments.options.length > 0 && !arguments.options[0].isEmpty()) {
			javadocargs = new String[numDefaultArguments + arguments.options.length];
			System.arraycopy(arguments.options, 0, javadocargs, numDefaultArguments, arguments.options.length);
		} else {
			javadocargs = new String[numDefaultArguments];
		}
		javadocargs[0] = "-d"; 
		javadocargs[1] = docOutput;
		javadocargs[2] = "-sourcepath";
		javadocargs[3] = srcOutput;
		if (args0 != null) {
			System.arraycopy(args0, 0, javadocargs, defaultArguments, args0.length);
		} 
		if (args1 != null) {
			System.arraycopy(args1, 0, javadocargs, defaultArguments + args0.length, args1.length);
		}
		
		for (int j = 0; j < javadocargs.length; j++) {
			System.out.println(javadocargs[j]);
		}
		
//		com.sun.tools.javadoc.Main.execute(javadocargs);
		workMonitor.worked();
		
		try {
			folder.refreshLocal(IFolder.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		workMonitor.worked();
		
		CorePlugin.getDefault().logInfo("Built Documentation");
	}
}
