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
package de.ovgu.featureide.core.mpl.job.statistics;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.TreeMap;

import org.eclipse.core.resources.IFolder;
import org.prop4j.Node;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.core.mpl.InterfaceProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.ProjectStructure;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.filter.ContextFilter;
import de.ovgu.featureide.core.signature.filter.FeatureFilter;
import de.ovgu.featureide.core.signature.filter.IFilter;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.io.IOConstants;
import de.ovgu.featureide.fm.core.job.AProjectJob;
import de.ovgu.featureide.fm.core.job.util.JobArguments;

/**
 * Builds different statistics from the {@link ProjectSignatures}.
 * 
 * @author Sebastian Krieter
 */
@SuppressWarnings("unused")
public class PrintStatisticsJob extends AProjectJob<PrintStatisticsJob.Arguments> {
	
	public static class Arguments extends JobArguments {
		private final String foldername;
		
		public Arguments(String foldername) {
			super(Arguments.class);
			this.foldername = foldername;
		}
	}
	
	private class Statistic {
		public static final int
			//MEMBER_CLASS = 0, MEMBER_FIELD = 1, MEMBER_METHOD = 2,
			CONTEXT_CONTEXT = 0, CONTEXT_MIN_VARIANTE1 = 1, CONTEXT_MIN_VARIANTE2 = 2, 
			CONTEXT_FEATURE = 3, DIFFERENCES = 4;
		private TreeMap<String, int[][]> sum = new TreeMap<String, int[][]>();
		
		public void set(int[] values, String feature, int context) {
			int[][] x = sum.get(feature);
			if (x == null) {
				x = new int[5][];
				sum.put(feature, x);
			}
			x[context] = values;
		}
		
		public String toCSVString() {
			StringBuilder sb = new StringBuilder();
			sb.append("feature;context_class;context_field;context_method;" +
					"minimum_class;minimum_field;minimum_method;" +
					"minFeatures_class;minFeatures_field;minFeatures_method;" +
					"feature_class;feature_field;feature_method;featureMinus;featurePlus\n");
			for (Entry<String, int[][]> entry : sum.entrySet()) {
				sb.append(entry.getKey());
				int[][] ar = entry.getValue();
				for (int i = 0; i < ar.length; i++) {
					int[] ar2 = ar[i];
					for (int j = 0; j < ar2.length; j++) {
						sb.append(';');
						sb.append(ar2[j]);
					}
				}
				sb.append('\n');
			}
			return sb.toString();
		}
	}
	
	private class SumStatistic {
		public static final int
			//MEMBER_CLASS = 0, MEMBER_FIELD = 1, MEMBER_METHOD = 2,
			CONTEXT_SPL = 0, CONTEXT_INTERFACE = 1, CONTEXT_ALWAYS = 2;
		private int[][] sum = new int[3][];
		
		public void set(int[] values, int context) {
			sum[context] = values;
		}
		
		public String toCSVString() {
			StringBuilder sb = new StringBuilder();
			sb.append("sum;class;field;method\nspl");
			
			int[] ar2 = sum[CONTEXT_SPL];
			for (int j = 0; j < ar2.length; j++) {
				sb.append(';');
				sb.append(ar2[j]);
			}
			sb.append("\ninterface");
			
			ar2 = sum[CONTEXT_INTERFACE];
			for (int j = 0; j < ar2.length; j++) {
				sb.append(';');
				sb.append(ar2[j]);
			}
			sb.append("\nalways");
			ar2 = sum[CONTEXT_ALWAYS];
			for (int j = 0; j < ar2.length; j++) {
				sb.append(';');
				sb.append(ar2[j]);
			}
			sb.append('\n');
			
			return sb.toString();
		}
	}
	
	private ContextFilter contextFilter;
	private int curFeatureID = -1;
	
	protected PrintStatisticsJob(Arguments arguments) {
		super("Create Statistics", arguments);
	}

	@Override
	protected boolean work() {
		InterfaceProject interfaceProject = MPLPlugin.getDefault().getInterfaceProject(this.project);
		if (interfaceProject == null) {
			MPLPlugin.getDefault().logWarning(this.project.getName() + " is no Interface Project!");
			return false;
		}
		IFolder folder = this.project.getFolder(arguments.foldername);
		IOConstants.clearFolder(folder);
		
		FeatureModel fm = interfaceProject.getFeatureModel();
		LinkedList<String> allConcreteFeatures = new LinkedList<String>();
		for (Feature feature : fm.getConcreteFeatures()) {
			allConcreteFeatures.add(feature.getName());
		}
		workMonitor.setMaxAbsoluteWork(allConcreteFeatures.size() + 1);
		
		HashMap<Integer, int[]> featureStatistics = interfaceProject.getProjectSignatures().getStatisticNumbers();
		Statistic stat = new Statistic();
		SumStatistic sumStat = new SumStatistic();

		sumStat.set(featureStatistics.get(-2), SumStatistic.CONTEXT_SPL);
		sumStat.set(featureStatistics.get(-3), SumStatistic.CONTEXT_INTERFACE);
		
		ProjectSignatures p = interfaceProject.getProjectSignatures();
		SignatureIterator it = p.iterator();
		it.addFilter(new ContextFilter(new Node[]{}, p));
		
		ProjectStructure ps = new ProjectStructure(it);
//		sumStat.set(ps.getStatisticsNumbers(), SumStatistic.CONTEXT_ALWAYS);
		sumStat.set(new int[0], SumStatistic.CONTEXT_ALWAYS);
		workMonitor.worked();
		
		IOConstants.writeToFile(folder.getFile("_sum_statistics.csv"), sumStat.toCSVString());
		
		Configuration defaultConf = new Configuration(fm, false);
		
		for (String featureName : allConcreteFeatures) {			
			Configuration conf = defaultConf.clone();
			conf.setManual(featureName, Selection.SELECTED);
			
			curFeatureID = interfaceProject.getFeatureID(featureName);
			contextFilter = new ContextFilter(IOConstants.buildNodeForFeature(featureName), p);
			
			it.clearFilter();
			it.addFilter(contextFilter);
			
			ProjectStructure contextSignature = new ProjectStructure(it);
			
			int[][] st = computeSolutionStatistics(interfaceProject, conf, folder, featureName, false);
			if (st != null) {
				stat.set(st[0], featureName, Statistic.CONTEXT_MIN_VARIANTE1);
				stat.set(st[1], featureName, Statistic.CONTEXT_MIN_VARIANTE2);
				
				int[] fstat = featureStatistics.get(curFeatureID);
				int[] c = new int[]{0,0,0};
				if (fstat != null) {
					c[0] = fstat[0];
					c[1] = fstat[2];
					c[2] = fstat[3];
				}

				stat.set(c, featureName, Statistic.CONTEXT_FEATURE);
//				stat.set(contextSignature.getStatisticsNumbers(), featureName, Statistic.CONTEXT_CONTEXT);
				stat.set(new int[0], featureName, Statistic.CONTEXT_CONTEXT);
				
				IFilter<AbstractSignature> featureFilter = new IFilter<AbstractSignature>() {
					@Override
					public boolean isValid(AbstractSignature signature) {
						return (signature.hasFeature(curFeatureID) > -1);
					}
				};
				int[] diff = new int[2];
				
				SignatureIterator it1 = p.iterator(); 
				SignatureIterator it2 = p.iterator();
				it1.addFilter(contextFilter);
				it2.addFilter(featureFilter);
				
				LinkedList<AbstractSignature>[] x = differentSignatures(it1, it2);
				diff[0] = x[0].size();
				diff[1] = x[1].size();
				StringBuilder sb = new StringBuilder();
				sb.append("Feature-");
				for (AbstractSignature sig : x[0]) {
					sb.append("\n\t");
					sb.append(sig.toString()); //.getFullName());
				}
				sb.append("\n\nFeature+");
				for (AbstractSignature sig : x[1]) {
					sb.append("\n\t");
					sb.append(sig.toString()); //.getFullName());
				}				
				
				stat.set(diff, featureName, Statistic.DIFFERENCES);
				IOConstants.writeToFile(folder.getFile("_diffFeature_" + featureName + ".txt"), sb.toString());
			}
			workMonitor.worked();
		}

		IOConstants.writeToFile(folder.getFile("_all_statistics.csv"), stat.toCSVString());
		MPLPlugin.getDefault().logInfo("Printed Statistics");
		return true;
	}

	private int[][] computeSolutionStatistics(InterfaceProject interfaceProject, Configuration conf, IFolder folder, String featureName, boolean fileOutput) {
		LinkedList<List<String>> solutionList;
		try {
			solutionList = conf.getSolutions(interfaceProject.getConfigLimit());
		} catch (TimeoutException e) {
			MPLPlugin.getDefault().logError(e);
			return null;
		}
		if (solutionList.isEmpty()) {
			return null;
		}

		int minNumFeatures = Integer.MAX_VALUE;
		LinkedList<List<String>> minSolutions = new LinkedList<List<String>>();
		
		while (!solutionList.isEmpty()) {
			List<String> featureList = solutionList.remove();
			
			int numFeatures = 0;
			for (String name : featureList) {
				Feature feature = conf.getFeatureModel().getFeature(name);
				if (feature != null && feature.isConcrete()) {
					numFeatures++;
				}
			}
			
			if (minNumFeatures > numFeatures) {
				minNumFeatures = numFeatures;
				minSolutions.clear();
				minSolutions.add(featureList);
			} else if (minNumFeatures == numFeatures) {
				minSolutions.add(featureList);
			}
		}
		
		int[] minNumbers2 = new int[3];
		int[] minNumbers = new int[3];
		minNumbers2[1] = 0;
		minNumbers2[2] = Integer.MAX_VALUE;
		Arrays.fill(minNumbers, Integer.MAX_VALUE);

		StringBuilder sb;
		if (fileOutput) {
			sb = new StringBuilder();
			sb.append("variant;classes;fields;methods");
		} else {
			sb = null;
		}
		int count = 0;

		StringBuilder differenceNumbers = new StringBuilder("minVarMinus;minVarPlus\n");
		StringBuilder differenceStrings = new StringBuilder();
		while (!minSolutions.isEmpty()) {
			int[] featureList = interfaceProject.getFeatureIDs(minSolutions.remove());
			
			ProjectSignatures projectSignatures = interfaceProject.getProjectSignatures();
			
			SignatureIterator it1 = projectSignatures.iterator(); 
			SignatureIterator it2 = projectSignatures.iterator();
			it1.addFilter(contextFilter);
			it2.addFilter(new FeatureFilter(featureList));
			
			ProjectStructure projectStructure = new ProjectStructure(it2);
			it2.reset();
			
//			AbstractSignature[] minVarCollection = projectSignatures.getAllMembers();
			LinkedList<AbstractSignature>[] y = differentSignatures(it1, it2);

			differenceNumbers.append(y[0].size());
			differenceNumbers.append(";");
			differenceNumbers.append(y[1].size());
			differenceNumbers.append("\n");
			
			differenceStrings.append("\n\n");
			differenceStrings.append(count);
			differenceStrings.append(":\nMinVar-");
			for (AbstractSignature sig : y[0]) {
				differenceStrings.append("\n\t");
				differenceStrings.append(sig.toString()); //.getFullName());
			}
			differenceStrings.append("\n\nMinVar+");
			for (AbstractSignature sig : y[1]) {
				differenceStrings.append("\n\t");
				differenceStrings.append(sig.toString()); //.getFullName());
			}
			
			int[] x = new int[0];
//			projectStructure.getStatisticsNumbers();
			
			if (fileOutput) {
				sb.append('\n');
				sb.append(count);
				for (int i = 0; i < x.length; i++) {
					sb.append(';');
					sb.append(x[i]);
				}
			}
			
			for (int i = 0; i < x.length; i++) {
				if (minNumbers[i] > x[i]) {
					minNumbers[i] = x[i];
				}
			}
			if (minNumbers2[1] + minNumbers2[2] > x[1] + x[2]) {
				minNumbers2 = x;
			}
			count++;			
		}
		if (fileOutput) {
			IOConstants.writeToFile(folder.getFile("variant_stats_" + featureName + ".csv"), sb.toString());
		}
		
		IOConstants.writeToFile(folder.getFile("_diffMinVarNumbers_" + featureName + ".csv"), differenceNumbers.toString());
		IOConstants.writeToFile(folder.getFile("_diffMinVar_" + featureName  + ".txt"), differenceStrings.toString());
		
		return new int[][]{minNumbers, minNumbers2};
	}
	
	@SuppressWarnings("unchecked")
	public LinkedList<AbstractSignature>[] differentSignatures(Iterator<AbstractSignature> sig1, Iterator<AbstractSignature> sig2) {
		final LinkedList<AbstractSignature> otherMembers = new LinkedList<AbstractSignature>();
		
		HashSet<AbstractSignature> testSet = new HashSet<AbstractSignature>();
		while (sig1.hasNext()) {
			AbstractSignature thisMember = sig1.next();
			if (!(thisMember instanceof AbstractClassSignature)) {
				testSet.add(thisMember);
			}
		}
		
		while (sig2.hasNext()) {
			AbstractSignature otherMember = sig2.next();
			if (!(otherMember instanceof AbstractClassSignature) && !testSet.remove(otherMember)) {
				otherMembers.add(otherMember);
			}
		}
		return new LinkedList[]{new LinkedList<AbstractSignature>(testSet), otherMembers};
	}
}
