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
package de.ovgu.featureide.core.mpl.io;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.TreeMap;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.prop4j.And;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.mpl.JavaInterfaceProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.io.constants.IOConstants;
import de.ovgu.featureide.core.mpl.signature.FeatureRoles;
import de.ovgu.featureide.core.mpl.signature.ProjectSignature;
import de.ovgu.featureide.core.mpl.signature.RoleMap;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassFragment;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractRole;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature;
import de.ovgu.featureide.core.mpl.signature.java.JavaClassCreator;
import de.ovgu.featureide.core.mpl.util.NumberConverter;
import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.configuration.SelectionNotPossibleException;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

/** 
 * Writes different types of interface files.
 * 
 * @author Sebastian Krieter
 */
public class InterfaceWriter extends AbstractWriter {
	
	private abstract class MonitorJob extends Job {
		private static final int maxRelativeWork = 100;
		
		protected IProgressMonitor monitor = null;
		private int relativeWorkDone, absoluteWorkDone, maxAbsoluteWork;
		
		public MonitorJob(String name) {
			this(name, Job.LONG);
		}
		
		public MonitorJob(String name, int priority) {
			super(name);
			setPriority(priority);
			schedule();
		}
		
		@Override
		public IStatus run(IProgressMonitor monitor) {
			this.monitor = monitor;
			relativeWorkDone = 0;
			absoluteWorkDone = 0;
			maxAbsoluteWork = 1;
			
			monitor.beginTask(getName(), maxRelativeWork);
			
			boolean ok = work();
			monitor.done();
			
			return ok ? Status.OK_STATUS : Status.CANCEL_STATUS;
		}
		
		protected void setMaxAbsoluteWork(int maxAbsoluteWork) {
			this.maxAbsoluteWork = maxAbsoluteWork;
		}

		protected void worked() {
			int nworked = (100 * ++absoluteWorkDone) / maxAbsoluteWork;
			if (nworked > relativeWorkDone) {
				monitor.worked(nworked - relativeWorkDone);
				relativeWorkDone = nworked;
			}
		}
		
		protected abstract boolean work();
	}
	
	private final class SignatureGroup implements Comparable<SignatureGroup> {
		private final int id;
		private final IFolder folder;
		private int size = 0;
		
		public SignatureGroup(int id, IFolder folder) {
			this.id = id;
			this.folder = folder;
		}
		
		public void addSig() {
			size++;
		}

		@Override
		public int compareTo(SignatureGroup otherSigGroup) {
			int dSize = size - otherSigGroup.size;
			return dSize != 0 ? dSize : otherSigGroup.id - id;
		}
	}	
	
	public InterfaceWriter(JavaInterfaceProject interfaceProject) {
		super(interfaceProject);
	}
	
	private String writeExtendedModule(ProjectSignature signature, String featureName, String folderName) {
		for (AbstractClassFragment curClass : signature.getClasses()) {
			AbstractClassSignature classSig = curClass.getSignature();
			final String packagename = classSig.getPackage();
			final String path = folderName + "/" + featureName + (packagename.isEmpty() ? "" :"/" + packagename);
			
			IFolder folder = CorePlugin.createFolder(interfaceProject.getProjectReference(), path);
			
			writeToFile(folder.getFile(classSig.getName() + IOConstants.EXTENSION_JAVA), curClass.toShortString());
		}
		
		IFolder folder = CorePlugin.createFolder(interfaceProject.getProjectReference(), folderName + "/" + featureName);		
		writeToFile(folder.getFile("statistics.txt"), signature.getStatisticsString());
		return signature.getStatisticsStringHeader();
	}
	
	public void createExtendedSignatures(final String folderName) {
		new MonitorJob("Build Extended Modules") {
			protected boolean work() {
				IFolder folder = interfaceProject.getProjectReference().getFolder(folderName);
				clearFolder(folder);
				
				LinkedList<String> allConcreteFeatures = new LinkedList<String>();
				for (Feature feature : interfaceProject.getFeatureModel().getConcreteFeatures()) {
					if (!feature.isHidden()) {
						allConcreteFeatures.add(feature.getName());
					}
				}
				setMaxAbsoluteWork(allConcreteFeatures.size() + 1);
				
				StringBuilder sb = new StringBuilder();
				sb.append("_No_Constraints_\n");
				sb.append(writeExtendedModule(buildSignature(new Node[]{}), "_No_Constraints_", folderName));
				worked();
				
				for (String featureName : allConcreteFeatures) {
					sb.append("\n");
					sb.append(featureName);
					sb.append("\n\n");
					sb.append(writeExtendedModule(buildSignature(buildNodeForFeature(featureName)), featureName, folderName));
					worked();
				}
				
				writeToFile(folder.getFile("all_statistics.txt"), sb.toString());
				
				MPLPlugin.getDefault().logInfo("Built Extended Modules");
				return true;
			}
		};
	}
	
	private void clearFolder(IFolder folder) {
		try {
			if (folder.exists()) {
				folder.delete(true, null);
			}
			folder.create(false, true, null);
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
		}
	}
	
	public void createStatistics(final String folderName) {
		new MonitorJob("Build Extended Modules") {
			protected boolean work() {
				IFolder folder = interfaceProject.getProjectReference().getFolder(folderName);
				clearFolder(folder);
				
				LinkedList<String> allConcreteFeatures = new LinkedList<String>();
				for (Feature feature : interfaceProject.getFeatureModel().getConcreteFeatures()) {
					if (!feature.isHidden()) {
						allConcreteFeatures.add(feature.getName());
					}
				}
				HashMap<String, int[]> featureStatistics = interfaceProject.getRoleMap().getStatisticNumbers();
				Configuration defaultConf = new Configuration(interfaceProject.getFeatureModel());
				Statistic stat = new Statistic();
				SumStatistic sumStat = new SumStatistic();
				
				setMaxAbsoluteWork(allConcreteFeatures.size() + 1);

				sumStat.set(featureStatistics.get("$$SPL"), SumStatistic.CONTEXT_SPL);
				sumStat.set(featureStatistics.get("$$INTERFACE"), SumStatistic.CONTEXT_INTERFACE);
				writeToFile(folder.getFile("_sum_statistics.csv"), sumStat.toCSVString());
				
				stat.set(new int []{0,0,0}, "_No_Feature_", Statistic.CONTEXT_FEATURE);
				stat.set(buildSignature(new Node[]{}).getStatisticsNumbers(), "_No_Feature_", Statistic.CONTEXT_CONTEXT);

				int[][] st = xyz(defaultConf, folder, "_No_Feature_");
				stat.set(st[0], "_No_Feature_", Statistic.CONTEXT_MIN_VARIANTE1);
				stat.set(st[1], "_No_Feature_", Statistic.CONTEXT_MIN_VARIANTE2);
				worked();
				
				for (String featureName : allConcreteFeatures) {
					int[] fstat = featureStatistics.get(featureName);
					int[] c = new int[]{0,0,0};
					if (fstat != null) {
						c[0] = fstat[0];
						c[1] = fstat[2];
						c[2] = fstat[3];
					}
					stat.set(c, featureName, Statistic.CONTEXT_FEATURE);
					stat.set(buildSignature(buildNodeForFeature(featureName)).getStatisticsNumbers(), 
							featureName, Statistic.CONTEXT_CONTEXT);
					
					Configuration conf = new Configuration(defaultConf, interfaceProject.getFeatureModel(), true);
					try {
						conf.setManual(featureName, Selection.SELECTED);
					} catch(SelectionNotPossibleException e) {
						conf.setAutomatic(featureName, Selection.SELECTED);
					}
					st = xyz(conf, folder, featureName);
					stat.set(st[0], featureName, Statistic.CONTEXT_MIN_VARIANTE1);
					stat.set(st[1], featureName, Statistic.CONTEXT_MIN_VARIANTE2);
					
					worked();
				}

				writeToFile(folder.getFile("_all_statistics.csv"), stat.toCSVString());
				MPLPlugin.getDefault().logInfo("Printed Statistics");
				return true;
			}
		};
		System.gc();
	}
	
	private static Node[] buildNodeForFeature(String featureName) {
		return new Node[] {new Literal(featureName, true)};		
	}
	
	public static ProjectSignature buildSignature(FeatureModel model, RoleMap map, String featureName){
		return buildSignature(model, map, buildNodeForFeature(featureName));
	}
	
	private ProjectSignature buildSignature(Node[] constraints) {
		ProjectSignature projectSig = new ProjectSignature(null, false);
		projectSig.setaClassCreator(new JavaClassCreator());
		
		Node[] fixClauses = new Node[constraints.length + 1];
		fixClauses[0] = NodeCreator.createNodes(interfaceProject.getFeatureModel());
		System.arraycopy(constraints, 0, fixClauses, 1, constraints.length);
		
		for (AbstractSignature sig : interfaceProject.getRoleMap().getSignatures()) {
			Node[] clauses = new Node[sig.getFeatures().size() + fixClauses.length];
			int j = 0;
			for (String featureName : sig.getFeatures()) {
				clauses[j++] = new Literal(featureName, false);
			}
			System.arraycopy(fixClauses, 0, clauses, j, fixClauses.length);
			
			SatSolver solver = new SatSolver(new And(clauses), 1000);
			try {
				if (!solver.isSatisfiable()) {
					projectSig.addSignature(sig);
				}
			} catch (TimeoutException e) {
				MPLPlugin.getDefault().logError(e);
			}
		}
		return projectSig;
	}
	
	private static ProjectSignature buildSignature(FeatureModel model, RoleMap map, Node[] constraints) {
		ProjectSignature projectSig = new ProjectSignature(null, false);
		projectSig.setaClassCreator(new JavaClassCreator());
		
		Node[] fixClauses = new Node[constraints.length + 1];
		fixClauses[0] = NodeCreator.createNodes(model);
		System.arraycopy(constraints, 0, fixClauses, 1, constraints.length);
		
		for (AbstractSignature sig : map.getSignatures()) {
			Node[] clauses = new Node[sig.getFeatures().size() + fixClauses.length];
			int j = 0;
			for (String featureName : sig.getFeatures()) {
				clauses[j++] = new Literal(featureName, false);
			}
			System.arraycopy(fixClauses, 0, clauses, j, fixClauses.length);
			
			SatSolver solver = new SatSolver(new And(clauses), 1000);
			try {
				if (!solver.isSatisfiable()) {
					projectSig.addSignature(sig);
				}
			} catch (TimeoutException e) {
				MPLPlugin.getDefault().logError(e);
			}
		}
		return projectSig;
	}
	
	private class Statistic {
		public static final int
			//MEMBER_CLASS = 0, MEMBER_FIELD = 1, MEMBER_METHOD = 2,
			CONTEXT_CONTEXT = 0, CONTEXT_MIN_VARIANTE1 = 1, CONTEXT_MIN_VARIANTE2 = 2, 
			CONTEXT_FEATURE = 3;
		private TreeMap<String, int[][]> sum = new TreeMap<String, int[][]>();
		
		public void set(int[] values, String feature, int context) {
			int[][] x = sum.get(feature);
			if (x == null) {
				x = new int[4][];
				sum.put(feature, x);
			}
			x[context] = values;
		}
		
		public String toCSVString() {
			StringBuilder sb = new StringBuilder();
			sb.append("feature;context_class;context_field;context_method;" +
					"minimum_class;minimum_field;minimum_method;" +
					"minFeatures_class;minFeatures_field;minFeatures_method;" +
					"feature_class;feature_field;feature_method\n");
			for (Entry<String, int[][]> entry : sum.entrySet()) {
				sb.append(entry.getKey());
				int[][] ar = entry.getValue();
				for (int i = 0; i < ar.length; i++) {
					int[] ar2 = ar[i];
					for (int j = 0; j < ar2.length; j++) {
						sb.append(";");
						sb.append(ar2[j]);
					}
				}
				sb.append("\n");
			}
			return sb.toString();
		}
	}
	
	private class SumStatistic {
		public static final int
			//MEMBER_CLASS = 0, MEMBER_FIELD = 1, MEMBER_METHOD = 2,
			CONTEXT_SPL = 0, CONTEXT_INTERFACE = 1;
		private int[][] sum = new int[2][];
		
		public void set(int[] values, int context) {
			sum[context] = values;
		}
		
		public String toCSVString() {
			StringBuilder sb = new StringBuilder();
			sb.append("sum;class;field;method\nspl");
			
			int[] ar2 = sum[CONTEXT_SPL];
			for (int j = 0; j < ar2.length; j++) {
				sb.append(";");
				sb.append(ar2[j]);
			}
			sb.append("\ninterface");
			
			ar2 = sum[CONTEXT_INTERFACE];
			for (int j = 0; j < ar2.length; j++) {
				sb.append(";");
				sb.append(ar2[j]);
			}
			sb.append("\n");
			
			return sb.toString();
		}
	}
	
	private int[][] xyz(Configuration conf, IFolder folder, String featureName) {
		LinkedList<List<String>> solutionList;
		try {
			solutionList = conf.getSolutions(interfaceProject.getConfigLimit());
		} catch (TimeoutException e) {
			MPLPlugin.getDefault().logError(e);
			return null;
		}
		
		int[][] minNumbers = new int[2][3];
		int[] minFeatures = new int[3];
		Arrays.fill(minNumbers[0], Integer.MAX_VALUE);
		Arrays.fill(minNumbers[1], Integer.MAX_VALUE);
		Arrays.fill(minFeatures, Integer.MAX_VALUE);

		StringBuilder sb = new StringBuilder();
		sb.append("variant;classes;fields;methods");
		int count = 0;
		
		while (!solutionList.isEmpty()) {
			List<String> featureList = solutionList.remove();
			
			int[] x = interfaceProject.getRoleMap().generateSignature(featureList, null).getStatisticsNumbers();
			sb.append("\n");
			sb.append(count++);
			for (int i = 0; i < x.length; i++) {
				sb.append(";");
				sb.append(x[i]);
			}
			for (int i = 0; i < x.length; i++) {
				if (minNumbers[0][i] > x[i]) {
					minNumbers[0][i] = x[i];
				}
				if (minFeatures[i] > featureList.size() 
						|| (minFeatures[i] == featureList.size() 
							&& minNumbers[1][i] > x[i])) {
					minFeatures[i] = featureList.size();
					minNumbers[1][i] = x[i];
				}
			}
		}
//		IFolder featureFolder = folder.getFolder(featureName);
//		clearFolder(featureFolder);
		writeToFile(folder.getFile("variant_stats_" + featureName + ".csv"), sb.toString());
		
		return minNumbers;
	}
	
	public void buildConfigurationInterfaces() {
		new MonitorJob("Build Configuration Interfaces") {
			@Override
			protected boolean work() {
				monitor.subTask("Calculate Solutions");
				
				final LinkedList<List<String>> solutionList;
				try {
					solutionList = interfaceProject.getConfiguration().getSolutions(interfaceProject.getConfigLimit());
				} catch (TimeoutException e) {
					MPLPlugin.getDefault().logError(e);
					return false;
				}
				final int numberSolutions = solutionList.size();
				
				monitor.subTask("Generate Signatures");
				
				IFolder interfaceFolder = interfaceProject.getProjectReference().getFolder("configuration_interfaces");
				IFolder groupListFolder = interfaceFolder.getFolder("groups");
				try {
					if (interfaceFolder.exists()) {
						interfaceFolder.delete(true, null);
					}
					interfaceFolder.create(false, true, null);
					groupListFolder.create(false, true, null);
				} catch (CoreException e) {
					MPLPlugin.getDefault().logError(e);
					return false;
				}

				final HashMap<ProjectSignature, SignatureGroup> signatureMap = new HashMap<ProjectSignature, SignatureGroup>();
				final NumberConverter converter = new NumberConverter(numberSolutions);
				
				int solutionId = 0, groupId = 0;
				setMaxAbsoluteWork(numberSolutions);
				
				int[][] minNumbers = new int[2][3];
				int[][] solutionIds = new int[2][3];
				int[][] groupIds = new int[2][3];
				int[] minFeatures = new int[3];
				Arrays.fill(minNumbers[0], Integer.MAX_VALUE);
				Arrays.fill(minNumbers[1], Integer.MAX_VALUE);
				Arrays.fill(minFeatures, Integer.MAX_VALUE);
				
				while (!solutionList.isEmpty()) {
					List<String> featureList = solutionList.remove();
					solutionId++;
					
					ProjectSignature sig = interfaceProject.getRoleMap().generateSignature(featureList, interfaceProject.getFilterViewTag());
					
					SignatureGroup sigGroup = signatureMap.get(sig);
					if (sigGroup == null) {
						sigGroup = new SignatureGroup(++groupId, groupListFolder.getFolder("interface_" + converter.convert(groupId)));
						signatureMap.put(sig, sigGroup);
					}
					
					sigGroup.addSig();
					IFolder groupFolder = sigGroup.folder;
					
					if (!groupFolder.exists()) {
						try {
							groupFolder.create(true, true, null);
							writeToFile(groupFolder.getFile("statistics.txt"), sig.getStatisticsString());
						} catch (CoreException e) {
							MPLPlugin.getDefault().logError(e);
							return false;
						}
					}
					
					int[] x = sig.getStatisticsNumbers();
					for (int i = 0; i < x.length; i++) {
						if (minNumbers[0][i] > x[i]) {
							minNumbers[0][i] = x[i];
							solutionIds[0][i] = solutionId;
							groupIds[0][i] = sigGroup.id;
						}
						if (minFeatures[i] > featureList.size() 
								|| (minFeatures[i] == featureList.size() 
									&& minNumbers[1][i] > x[i])) {
							minFeatures[i] = featureList.size();
							minNumbers[1][i] = x[i];
							solutionIds[1][i] = solutionId;
							groupIds[1][i] = sigGroup.id;
						}
					}
					
					writeSolutionList(featureList, groupFolder.getFile("featureList_" + converter.convert(solutionId) + IOConstants.EXTENSION_SOLUTION));
					worked();
				}
				
				StringBuilder sb2 = new StringBuilder();
				sb2.append("Min #Classes: ");
				sb2.append(minNumbers[0][0]);
				sb2.append(" (Solution ");
				sb2.append(converter.convert(solutionIds[0][0]));
				sb2.append(" in Group ");
				sb2.append(converter.convert(groupIds[0][0]));
				sb2.append(")\n");

				sb2.append("Min #Fields: ");
				sb2.append(minNumbers[0][1]);
				sb2.append(" (Solution ");
				sb2.append(converter.convert(solutionIds[0][1]));
				sb2.append(" in Group ");
				sb2.append(converter.convert(groupIds[0][1]));
				sb2.append(")\n");

				sb2.append("Min #Methods: ");
				sb2.append(minNumbers[0][2]);
				sb2.append(" (Solution ");
				sb2.append(converter.convert(solutionIds[0][2]));
				sb2.append(" in Group ");
				sb2.append(converter.convert(groupIds[0][2]));
				sb2.append(")\n");
				
				writeToFile(interfaceFolder.getFile("Min_Statistics.txt"), sb2.toString());
				
				SignatureGroup[] signatureArray = new SignatureGroup[signatureMap.size()];
				signatureMap.values().toArray(signatureArray);
				Arrays.sort(signatureArray);
				
				if (signatureArray.length > 0) {
					int curNumber = signatureArray[signatureArray.length - 1].size;
					int count = 0;
					final StringBuilder sb = new StringBuilder("Number of Solutions -> IDs");
					sb.append(LINE_SEPARATOR);
					sb.append(LINE_SEPARATOR);
					sb.append(curNumber);
					
					for (int i = signatureArray.length - 1; i >= 0; i--) {
						SignatureGroup sigGroup = signatureArray[i];
						if (curNumber > sigGroup.size) {
							curNumber = sigGroup.size;
							sb.append(LINE_SEPARATOR);
							sb.append("\tCount : ");
							sb.append(count);
							count = 0;
							sb.append(LINE_SEPARATOR);
							sb.append(curNumber);
						}
						sb.append(count++ == 0 ? ':' + LINE_SEPARATOR + "\tIDs   : " : ", ");
						sb.append(converter.convert(sigGroup.id));
					}

					sb.append(LINE_SEPARATOR);
					sb.append("\tCount : ");
					sb.append(count);
					
					writeToFile(interfaceFolder.getFile("NumberOfSolutions.txt"), sb.toString());
				}
				
				MPLPlugin.getDefault().logInfo("Built Configuration Interfaces: " + signatureMap.size() + " / " + numberSolutions);
				return true;
			}
		};
	}
	
	public void compareConfigurationInterfaces() {
		new MonitorJob("Compare Configuration Interfaces") {
			@Override
			protected boolean work() {
				monitor.subTask("Calculate Solutions");
				
				final int configLimit = interfaceProject.getConfigLimit();
				
				final LinkedList<List<String>> solutionList;
				try {
					solutionList = interfaceProject.getConfiguration().getSolutions(configLimit);
				} catch (TimeoutException e) {
					MPLPlugin.getDefault().logError(e);
					return false;
				}
				
				monitor.subTask("Generate Signatures");
				
				final HashSet<ProjectSignature> signatures = new HashSet<ProjectSignature>();
				
				final LinkedList<ProjectSignature> signaturesList = new LinkedList<ProjectSignature>();
				final LinkedList<Integer> groupIdList = new LinkedList<Integer>();
				
				final NumberConverter converter = new NumberConverter(solutionList.size());
				int groupId = 0;
				
				while (!solutionList.isEmpty()) {
					ProjectSignature sig = interfaceProject.getRoleMap().generateSignature(solutionList.remove(), interfaceProject.getFilterViewTag());
					if (signatures.add(sig)) {
						signaturesList.add(sig);
						groupIdList.add(++groupId);
					}
				}
				final int 
					numberSignatures = signatures.size(),
					numberCompares = (numberSignatures*(numberSignatures - 1)) >> 1;
				
				monitor.subTask("Compare Signatures");
				setMaxAbsoluteWork(numberCompares);
				
				final double[] compareValues = new double[numberCompares];
				int compareIndex = 0;
				
				while (!signaturesList.isEmpty()) {
					ProjectSignature sig = signaturesList.remove();
					for (ProjectSignature otherSig : signaturesList) {
						compareValues[compareIndex++] = sig.similarityTo(otherSig);
						worked();
					}	
				}
				
				final StringBuilder similarityQString = new StringBuilder();
				for (int id : groupIdList) {
					similarityQString.append(converter.convert(id));
					similarityQString.append(',');
				}
				similarityQString.deleteCharAt(similarityQString.length() - 1);
				similarityQString.append(LINE_SEPARATOR);

				for (int i = 0; i < numberSignatures; i++) {
					for (int j = 0; j < numberSignatures; j++) {
						if (i < j) {
							similarityQString.append(compareValues[getIndex(i, j, numberSignatures)]);
						} else if (i > j) {
							similarityQString.append(compareValues[getIndex(j, i, numberSignatures)]);
						} else {
							similarityQString.append("1.0");
						}
						similarityQString.append(',');
					}
					similarityQString.deleteCharAt(similarityQString.length() - 1);
					similarityQString.append(LINE_SEPARATOR);
				}
				writeToFile(interfaceProject.getProjectReference().getFile(IOConstants.FILENAME_COMPARE_MATRIX), similarityQString.toString());
				MPLPlugin.getDefault().logInfo("Compared " + numberSignatures + " different Interfaces");
				return true;
			}
		};
	}
	
	private int getIndex(int i, int j, int max) {
		return j + (i * max) - (((i + 3) * i) >> 1) - 1;
	}
	
	private void writeSolutionList(List<String> featureList, IFile outputFile) {
		final StringBuilder solutionString = new StringBuilder();
		for (String featureName : featureList) {
			solutionString.append(featureName);
			solutionString.append(LINE_SEPARATOR);
		}
		writeToFile(outputFile, solutionString.toString());
	}

	public void buildFeatureInterfaces() {
		buildFeatureInterfaces(true, MPLPlugin.WRAPPER_INTERFACES 
				? IOConstants.FOLDERNAME_WRAPPER_INTERFACES 
				: IOConstants.FOLDERNAME_FEATURE_INTERFACES, false);
	}
	
	public void buildAllFeatureInterfaces(boolean reduced) {
		buildFeatureInterfaces(true, IOConstants.FOLDERNAME_FEATURE_ROLES, reduced);
	}
	
	public void buildAllFeatureInterfaces(String folderName) {
		buildFeatureInterfaces(true, folderName, false);
	}
	
	public void buildFeatureInterfaces(final boolean all, final String foldername, final boolean reduced) {
		new MonitorJob("Build Feature Interfaces") {
			protected boolean work() {
				RoleMap roleMap;
				if (reduced) {
					roleMap = new RoleMap(interfaceProject.getRoleMap(), interfaceProject.getFilterViewTag());
				} else {
					roleMap = interfaceProject.getRoleMap();
				}
				List<SelectableFeature> features = interfaceProject.getConfiguration().getFeatures();

				IFolder folder = CorePlugin.createFolder(interfaceProject.getProjectReference(), foldername);
				
				try {
					folder.delete(true, null);
				} catch (CoreException e) {
					MPLPlugin.getDefault().logError(e);
					return false;
				}
		
				setMaxAbsoluteWork(features.size());
				
				for (SelectableFeature feature : features) {
					if (all || feature.getSelection() != Selection.UNSELECTED) {
						FeatureRoles roles = roleMap.getRoles(feature.getName());
						if (roles != null) {
							for (AbstractRole role : roles) {
		
								String packagename = role.getSignature().getPackage();
								
								String path = foldername + "/" + feature.getName() +
									(MPLPlugin.WRAPPER_INTERFACES ? "__Wrapper" : "") + 
									(packagename.isEmpty() ? "" :"/" + packagename);
								
								folder = CorePlugin.createFolder(interfaceProject.getProjectReference(), path);
		
								if (all) {
									writeToFile(folder.getFile(role.getSignature().getName() + IOConstants.EXTENSION_JAVA), role.toShortString());
								} else {
									writeToFile(folder.getFile(role.getSignature().getName() + IOConstants.EXTENSION_JAVA), role.toString());
								}
								
							}
						}
					}
					worked();
				}
				if (MPLPlugin.WRAPPER_INTERFACES) {
					dublicateFeatureModel(CorePlugin.createFolder(interfaceProject.getProjectReference(), foldername));
					MPLPlugin.getDefault().logInfo("Built Wrapper Interfaces");
					
					MPLPlugin.PRIVATE_METHODS = false;
					MPLPlugin.WRAPPER_INTERFACES = false;
				} else {
					if (all) {
//						writeToFile(interfaceProject.getProjectReference().getFile("SPL_Statistic.txt"), 
//								roleMap.getStatisticsString());
					} else {
						MPLPlugin.getDefault().logInfo("Built Feature Interfaces");
					}
				}
				interfaceProject.refreshRoleMap();
				if (all) {
					roleMap = interfaceProject.getRoleMap();
					writeToFile(interfaceProject.getProjectReference().getFile("SPL_Statistic.txt"), 
							roleMap.getStatisticsString());
				}
				
				return true;
			}
		};
	}
	
	private void dublicateFeatureModel(IFolder folder) {		
		FeatureModel fm = FileLoader.loadFeatureModel(interfaceProject);
		fm.clone();
		Feature root = fm.getRoot();
		
		Feature newRoot = new Feature(fm, "_Wrapper__Root_");
		newRoot.addChild(root);
		fm.addFeature(newRoot);
		fm.setRoot(newRoot);
		
		dublicateFeatureModel_rec(fm, root, newRoot);
		
		new FeatureModelWriter().writeModel(fm, folder.getFile(IOConstants.FILENAME_MODEL));
	}
	
	private void dublicateFeatureModel_rec(FeatureModel fm, Feature orginalFeature, Feature wrapperParent) {
    	if (orginalFeature != null) {
    		LinkedList<Feature> children = orginalFeature.getChildren();
        	
    		Feature wrapperFeature = new Feature(fm, orginalFeature.getName() + "__Wrapper");
    		wrapperFeature.setMandatory(orginalFeature.isMandatory());
    		wrapperFeature.setAbstract(orginalFeature.isAbstract());
    		wrapperFeature.setHidden(orginalFeature.isHidden());
    		wrapperFeature.setMultiple(orginalFeature.isMultiple());
    		if (orginalFeature.isAnd()) {
    			wrapperFeature.setAnd();
    		} else if (orginalFeature.isOr()) {
    			wrapperFeature.setOr();
    		} else if (orginalFeature.isAlternative()) {
    			wrapperFeature.setAlternative();
	    	}
    		
    		fm.addFeature(wrapperFeature);
    		wrapperParent.addChild(wrapperFeature);
    		
    		Node node = new Implies(
    				new Literal(wrapperFeature.getName()), 
    				new Literal(orginalFeature.getName()));
    		
    		fm.addConstraint(new Constraint(fm, node));
    		
	    	Iterator<Feature> i = children.iterator();
	    	while (i.hasNext()) {
	    		dublicateFeatureModel_rec(fm ,i.next(), wrapperFeature);
	    	}
    	}    	
    }
}
