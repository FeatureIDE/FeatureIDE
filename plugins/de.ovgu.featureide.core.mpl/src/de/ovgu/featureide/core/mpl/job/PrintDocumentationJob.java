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

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.mpl.InterfaceProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.io.IOConstants;
import de.ovgu.featureide.core.mpl.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.mpl.signature.ProjectStructure;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassFragment;
import de.ovgu.featureide.core.mpl.signature.filter.ContextFilter;
import de.ovgu.featureide.core.mpl.signature.filter.FeatureFilter;
import de.ovgu.featureide.core.mpl.signature.javadoc.AJavaDocCommentMerger;
import de.ovgu.featureide.core.mpl.signature.javadoc.ContextMerger;
import de.ovgu.featureide.core.mpl.signature.javadoc.FeatureModuleMerger;
import de.ovgu.featureide.core.mpl.signature.javadoc.SPLMerger;
import de.ovgu.featureide.core.mpl.signature.javadoc.VariantMerger;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationReader;
import de.ovgu.featureide.fm.core.job.AProjectJob;
import de.ovgu.featureide.fm.core.job.util.JobArguments;

/**
 * Builds the JavaDoc-Documentation.
 * 
 * @author Sebastian Krieter
 */
public class PrintDocumentationJob extends AProjectJob<PrintDocumentationJob.Arguments> {
	
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
	
	protected PrintDocumentationJob(Arguments arguments) {
		super("Build Documentation", arguments);
	}

	@Override
	protected boolean work() {
		InterfaceProject interfaceProject = MPLPlugin.getDefault().getInterfaceProject(this.project);
		if (interfaceProject == null) {
			MPLPlugin.getDefault().logWarning(this.project.getName() + " is no Interface Project!");
			return false;
		}
		IFolder folder = CorePlugin.createFolder(this.project, arguments.foldername);
		final String folderPath = folder.getLocation().toOSString();
		
		try {
			folder.delete(true, null);
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}

		final String extFoldername = arguments.foldername + "/src/";
		
		CorePlugin.createFolder(this.project, extFoldername);
		
		final SignatureIterator it = interfaceProject.getProjectSignatures().createIterator();
		AJavaDocCommentMerger merger = null;
		
		int[] featureIDs = new int[interfaceProject.getFeatureCount()];
		int i = 0;
		for (String string : interfaceProject.getFeatureModel().getFeatureOrderList()) {
			featureIDs[i++] = interfaceProject.getFeatureID(string);
		}
		int index = -1;
		if (arguments.featurename != null) {
			index = interfaceProject.getFeatureID(arguments.featurename);
		}
		
		switch (arguments.mode) {
		// ----------------------------------- SPL ---------------------------------------------
		case 0: 
			merger = new SPLMerger(interfaceProject, featureIDs);
			break;
			
		// -------------------------------- Variante ---------------------------------------------
		case 1:
			Configuration conf = new Configuration(interfaceProject.getFeatureModel());
			try {
				IFile file = interfaceProject.getFeatureProjectReference().getCurrentConfiguration();
				new ConfigurationReader(conf).readFromFile(file);
			} catch (Exception e) {
				MPLPlugin.getDefault().logError(e);
				return false;
			}
			final List<Feature> featureSet = conf.getSelectedFeatures();
			final int[] tempFeatureList = new int[featureSet.size()];
			int count = 0;
			for (Feature selctedFeature : featureSet) {
				final int id = interfaceProject.getFeatureID(selctedFeature.getName());
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
			merger = new VariantMerger(interfaceProject, featureList);
			break;
			
		// --------------------------------- Context ---------------------------------------------
		case 2:
			if (index > -1) {
				it.addFilter(new ContextFilter(arguments.featurename, interfaceProject));
				merger = new ContextMerger(interfaceProject, featureIDs);
			}
			break;
			
		// ------------------------------- Featuremodul ------------------------------------------
		case 3:
			if (index > -1) {
				int[] shortFeatureIDs = null;
				for (int j = 0; j < featureIDs.length; j++) {
					if (index == featureIDs[j]) {
						shortFeatureIDs = new int[j + 1];
						System.arraycopy(featureIDs, 0, shortFeatureIDs, 0, j + 1);
						break;
					}
				}
				if (shortFeatureIDs == null) {
					//warning?
					return false;
				}
				
//				it.addFilter(new ContextFilter(arguments.featurename, interfaceProject));
//				it.addFilter(new FeatureFilter(shortFeatureIDs));
				it.addFilter(new FeatureFilter(new int[]{index}));
				merger = new FeatureModuleMerger(interfaceProject, shortFeatureIDs, index);
			}
			break;
			
		default:
			return false;
		}
		
		if (merger == null) {
			return false;
		}
		while (it.hasNext()) {
			merger.setSig(it.next());
			merger.mergeComments();
		}
		it.reset();

		final HashSet<String> packageSet = new HashSet<String>();
		final LinkedList<String> classList = new LinkedList<String>();
		final ProjectStructure structure = new ProjectStructure(it);
		final String docOutput = folderPath + "\\doc\\";
		final String srcOutput = folderPath + "\\src\\";
		
		setMaxAbsoluteWork(structure.getClasses().size() + 2);
		
		for (AbstractClassFragment javaClass : structure.getClasses()) {
			String packagename = javaClass.getSignature().getPackage();
			
			String path = extFoldername + packagename.replace('.', '/');
			
			if (packagename.isEmpty()) {
				classList.add(srcOutput + javaClass.getSignature().getName() + IOConstants.EXTENSION_JAVA);
			} else {
				packageSet.add(packagename);
			}
			
			folder = CorePlugin.createFolder(interfaceProject.getProjectReference(), path);
			IOConstants.writeToFile(
					folder.getFile(javaClass.getSignature().getName() + IOConstants.EXTENSION_JAVA),
					javaClass.toString());
			worked();
		}
		folder = CorePlugin.createFolder(interfaceProject.getProjectReference(), arguments.foldername + "/doc/");
		
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
		
		com.sun.tools.javadoc.Main.execute(javadocargs);
		worked();
		
		try {
			folder.refreshLocal(IFolder.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
		}
		worked();
		
		MPLPlugin.getDefault().logInfo("Built Documentation");
		return true;
	}
}
