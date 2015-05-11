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

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.fm.core.io.IOConstants;
import de.ovgu.featureide.fm.core.job.AProjectJob;
import de.ovgu.featureide.fm.core.job.util.JobArguments;

/** 
 * @author Sebastian Krieter
 */
public class PrintDocumentationStatisticsJob extends AProjectJob<PrintDocumentationStatisticsJob.Arguments> {
	
	public static class Arguments extends JobArguments {
		private final String foldername;
		
		public Arguments(String foldername) {
			super(Arguments.class);
			this.foldername = foldername;
		}
	}
	
	protected PrintDocumentationStatisticsJob(Arguments arguments) {
		super("Build Documentation Statistics", arguments);
	}

	@Override
	protected boolean work() {
		final IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
		if (featureProject == null) {
			CorePlugin.getDefault().logWarning(this.project.getName() + " is no FeatureIDE Project!");
			return false;
		}
		
		IFolder folder = CorePlugin.createFolder(this.project, arguments.foldername);
		try {
			folder.delete(true, null);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
			return false;
		}
		CorePlugin.createFolder(this.project, arguments.foldername);
		
		final ProjectSignatures projectSignatures = featureProject.getProjectSignatures();
		if (projectSignatures == null) {
			CorePlugin.getDefault().logWarning("No signatures available!");
			return false;
		}
		
		int[] featureIDs = new int[projectSignatures.getFeatureCount()];
		int i = 0;
		for (String string : projectSignatures.getFeatureModel().getFeatureOrderList()) {
			featureIDs[i++] = projectSignatures.getFeatureID(string);
		}

		workMonitor.setMaxAbsoluteWork(2 * featureIDs.length + 5);

		int[] statisticDataChars = new int[5];
		int[] statisticDataTags = new int[5];
		
		
		// ----------------------------------- SPL ---------------------------------------------
//		AJavaDocCommentMerger.reset();
//		pseudoMerge(interfaceProject.getProjectSignatures().createIterator(),
//			new SPLMerger(interfaceProject, featureIDs));
//		statisticDataChars[0] = AJavaDocCommentMerger.STAT_BEFORE_CHARS;
//		statisticDataChars[2] = AJavaDocCommentMerger.STAT_AFTER_CHARS;
//		statisticDataTags[0] = AJavaDocCommentMerger.STAT_BEFORE_TAGS;
//		statisticDataTags[2] = AJavaDocCommentMerger.STAT_AFTER_TAGS;

//		int[] statisticNumComments = new int[]{
//			AJavaDocCommentMerger.STAT_NUM_FEATURE0,
//			AJavaDocCommentMerger.STAT_NUM_FEATURE1,
//			AJavaDocCommentMerger.STAT_NUM_NEW,
//			AJavaDocCommentMerger.STAT_NUM_FEATURE0 + AJavaDocCommentMerger.STAT_NUM_FEATURE1,
//			AJavaDocCommentMerger.STAT_NUM_GENERAL0,
//			AJavaDocCommentMerger.STAT_NUM_GENERAL1,
//			AJavaDocCommentMerger.STAT_NUM_GENERAL0 + AJavaDocCommentMerger.STAT_NUM_GENERAL1,
//			AJavaDocCommentMerger.STAT_NUM_FEATURE0 + AJavaDocCommentMerger.STAT_NUM_FEATURE1 +
//			AJavaDocCommentMerger.STAT_NUM_GENERAL0 + AJavaDocCommentMerger.STAT_NUM_GENERAL1,
//		};
		workMonitor.worked();
			
		// ------------------------------- Featuremodule ------------------------------------------

//		AJavaDocCommentMerger.reset();
//		for (int j = 0; j < featureIDs.length; j++) {
//			int[] shortFeatureIDs = new int[j + 1];
//			System.arraycopy(featureIDs, 0, shortFeatureIDs, 0, j + 1);
//
//			SignatureIterator it = interfaceProject.getProjectSignatures().createIterator();
//			it.addFilter(new FeatureFilter(new int[]{j}));
//			pseudoMerge(it, new FeatureModuleMerger(interfaceProject, shortFeatureIDs, j));
//			workMonitor.worked();
//		}
//		statisticDataChars[4] = AJavaDocCommentMerger.STAT_AFTER_CHARS;
//		statisticDataTags[4] = AJavaDocCommentMerger.STAT_AFTER_TAGS;

		// --------------------------------- Context ---------------------------------------------
//		AJavaDocCommentMerger.reset();
//		SignatureIterator it = interfaceProject.getProjectSignatures().createIterator();
//		it.addFilter(new ContextFilter(new Node[]{}, interfaceProject));
//		pseudoMerge(it, new ContextMerger(interfaceProject, featureIDs));
//		statisticDataChars[3] = AJavaDocCommentMerger.STAT_AFTER_CHARS;
//		statisticDataTags[3] = AJavaDocCommentMerger.STAT_AFTER_TAGS;
//		for (int j = 0; j < featureIDs.length; j++) {
//			it = interfaceProject.getProjectSignatures().createIterator();
//			it.addFilter(new ContextFilter(interfaceProject.getFeatureName(j), interfaceProject));
//			pseudoMerge(it, new ContextMerger(interfaceProject, featureIDs));
//
//			AJavaDocCommentMerger.STAT_AFTER_CHARS -= statisticDataChars[3];
//			AJavaDocCommentMerger.STAT_AFTER_TAGS -= statisticDataTags[3];
//			workMonitor.worked();
//		}
//		statisticDataChars[3] += AJavaDocCommentMerger.STAT_AFTER_CHARS;
//		statisticDataTags[3] += AJavaDocCommentMerger.STAT_AFTER_TAGS;
		
		// -------------------------------- Variante ---------------------------------------------

		statisticDataChars[1] = statisticDataChars[0];
		statisticDataTags[1] = statisticDataTags[0];
		workMonitor.worked();
		
		// ------------------------------------------------------------------------------------------------------------
		
		StringBuilder sb = new StringBuilder("MyMethod;Variant;SPL;Context;FeatureModule;Sum\n");
		
		int sum = -statisticDataChars[0];
		for (int j = 0; j < statisticDataChars.length; j++) {
			sb.append(statisticDataChars[j]);
			sb.append(';');
			sum += statisticDataChars[j];
		}
		sb.append(sum);
		sb.append('\n');
		
		int sum2 = -statisticDataTags[0];
		for (int j = 0; j < statisticDataTags.length; j++) {
			sb.append(statisticDataTags[j]);
			sb.append(';');
			sum2 += statisticDataTags[j];
		}
		sb.append(sum2);
		sb.append('\n');
		IOConstants.writeToFile(folder.getFile("statistics.csv"), sb.toString());
		workMonitor.worked();
		
		StringBuilder sb2 = new StringBuilder();
		
		String[] texString = new String[]{"Verfahren","Variante","SPL","Kontext","Featuremodul","Summe"};
		for (int j = 0; j < statisticDataTags.length; j++) {
			sb2.append(texString[j]);
			sb2.append(" & ");
			sb2.append(statisticDataChars[j]);
			sb2.append(" & ");
			sb2.append((int)(100 * ((double)statisticDataChars[j])/((double)statisticDataChars[0])));
			sb2.append("\\% & ");
			sb2.append(statisticDataTags[j]);
			sb2.append(" & ");
			sb2.append((int)(100 * ((double)statisticDataTags[j])/((double)statisticDataTags[0])));
			sb2.append("\\% \\\\\n");
		}
		sb2.append(texString[statisticDataTags.length]);
		sb2.append(" & ");
		sb2.append(sum);
		sb2.append(" & ");
		sb2.append((int)(100 * ((double)sum)/((double)statisticDataChars[0])));
		sb2.append("\\% & ");
		sb2.append(sum2);
		sb2.append(" & ");
		sb2.append((int)(100 * ((double)sum2)/((double)statisticDataTags[0])));
		sb2.append("\\% \\\\\n");

		IOConstants.writeToFile(folder.getFile("latexTab.txt"), sb2.toString());
		workMonitor.worked();
		
		StringBuilder sb3 = new StringBuilder("Feature0;Feature1;New;SumFeature;General0;General1;SumGeneral;SumAll\n");
//		for (int j = 0; j < statisticNumComments.length; j++) {
//			sb3.append(statisticNumComments[j]);
//			sb3.append(';');						
//		}
		sb3.setCharAt(sb3.length() - 1, '\n');
		IOConstants.writeToFile(folder.getFile("numComments.txt"), sb3.toString());
		workMonitor.worked();
		
		CorePlugin.getDefault().logInfo("Built Documentation Statistics");
		return true;
	}
	
//	private void pseudoMerge(SignatureIterator it, ADocumentationCommentMerger merger) {
//		while (it.hasNext()) {
//			merger.setSig(it.next());
//			merger..mergeComments();
//		}
//	}
}
