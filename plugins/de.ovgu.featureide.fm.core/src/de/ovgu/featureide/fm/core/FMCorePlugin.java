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
package de.ovgu.featureide.fm.core;

import static de.ovgu.featureide.fm.core.localization.StringTable.PRINTED_OUTPUT_FILE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.READING_MODEL_FILE___;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.osgi.framework.BundleContext;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeatureModel.UsedModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.cnf.UnkownLiteralException;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.FileManagerMap;
import de.ovgu.featureide.fm.core.job.IJob;
import de.ovgu.featureide.fm.core.job.IProjectJob;
import de.ovgu.featureide.fm.core.job.util.JobArguments;
import de.ovgu.featureide.fm.core.job.util.JobSequence;

/**
 * The activator class controls the plug-in life cycle.
 * 
 * @author Thomas Thuem
 */
public class FMCorePlugin extends AbstractCorePlugin {

	public static final String PLUGIN_ID = "de.ovgu.featureide.fm.core";

	private static FMCorePlugin plugin;

	@Override
	public String getID() {
		return PLUGIN_ID;
	}

	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
	}

	public void stop(BundleContext context) throws Exception {
		plugin = null;
		super.stop(context);
	}

	public static FMCorePlugin getDefault() {
		return plugin;
	}

	/**
	 * Creates a {@link IProjectJob} for every project with the given arguments.
	 * 
	 * @param projects the list of projects
	 * @param arguments the arguments for the job
	 * @param autostart if {@code true} the jobs is started automatically.
	 * @return the created job or a {@link JobSequence} if more than one project is given.
	 *         Returns {@code null} if {@code projects} is empty.
	 */
	public IJob startJobs(List<IProject> projects, JobArguments arguments, boolean autostart) {
		IJob ret;
		switch (projects.size()) {
		case 0:
			return null;
		case 1:
			IProjectJob newJob = arguments.createJob();
			newJob.setProject(projects.get(0));
			ret = newJob;
			break;
		default:
			final JobSequence jobSequence = new JobSequence();
			jobSequence.setIgnorePreviousJobFail(true);
			for (IProject p : projects) {
				IProjectJob newSequenceJob = arguments.createJob();
				newSequenceJob.setProject(p);
				jobSequence.addJob(newSequenceJob);
			}
			ret = jobSequence;
		}
		if (autostart) {
			ret.schedule();
		}
		return ret;
	}

	public void analyzeModel(IFile file) {
		logInfo(READING_MODEL_FILE___);
		final IContainer outputDir = file.getParent();
		if (outputDir == null || !(outputDir instanceof IFolder)) {
			return;
		}

		final IPersistentFormat<IFeatureModel> format = FeatureModelManager.getFormat(file.getName());
		if (format == null) {
			return;
		}

		final String path = file.getLocation().toString();
		if (FileManagerMap.hasInstance(path)) {
			final FeatureModelManager instance = FileManagerMap.<IFeatureModel, FeatureModelManager> getInstance(path);
			final IFeatureModel fm = instance.getObject();

			try {
				FeatureModelAnalyzer fma = new FeatureModelAnalyzer(fm);
				fma.analyzeFeatureModel(null);

				final StringBuilder sb = new StringBuilder();
				sb.append("Number Features: ");
				sb.append(fm.getNumberOfFeatures());
				sb.append(" (");
				sb.append(fma.countConcreteFeatures());
				sb.append(")\n");

				if (fm instanceof ExtendedFeatureModel) {
					ExtendedFeatureModel extFeatureModel = (ExtendedFeatureModel) fm;
					int countInherited = 0;
					int countInstances = 0;
					for (UsedModel usedModel : extFeatureModel.getExternalModels().values()) {
						switch (usedModel.getType()) {
						case ExtendedFeature.TYPE_INHERITED:
							countInherited++;
							break;
						case ExtendedFeature.TYPE_INSTANCE:
							countInstances++;
							break;
						}
					}
					sb.append("Number Instances: ");
					sb.append(countInstances);
					sb.append("\n");
					sb.append("Number Inherited: ");
					sb.append(countInherited);
					sb.append("\n");
				}

				final List<List<IFeature>> unnomralFeature = fma.analyzeFeatures();

				Collection<IFeature> analyzedFeatures = unnomralFeature.get(0);
				sb.append("Core Features (");
				sb.append(analyzedFeatures.size());
				sb.append("): ");
				for (IFeature coreFeature : analyzedFeatures) {
					sb.append(coreFeature.getName());
					sb.append(", ");
				}
				analyzedFeatures = unnomralFeature.get(1);
				sb.append("\nDead Features (");
				sb.append(analyzedFeatures.size());
				sb.append("): ");
				for (IFeature deadFeature : analyzedFeatures) {
					sb.append(deadFeature.getName());
					sb.append(", ");
				}
				analyzedFeatures = fma.getFalseOptionalFeatures();
				sb.append("\nFO Features (");
				sb.append(analyzedFeatures.size());
				sb.append("): ");
				for (IFeature foFeature : analyzedFeatures) {
					sb.append(foFeature.getName());
					sb.append(", ");
				}
				sb.append("\n");

				final IFile outputFile = ((IFolder) outputDir).getFile(file.getName() + "_output.txt");
				final InputStream inputStream = new ByteArrayInputStream(sb.toString().getBytes(Charset.defaultCharset()));
				if (outputFile.isAccessible()) {
					outputFile.setContents(inputStream, false, true, null);
				} else {
					outputFile.create(inputStream, true, null);
				}
				logInfo(PRINTED_OUTPUT_FILE_);
			} catch (Exception e) {
				logError(e);
			}
		}
	}
	
	public void removeFeatures(IProject project, IFeatureModel data, Collection<String> features) {
		try {
			removeFeatures(data, features);
		} catch (TimeoutException | UnkownLiteralException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	public static Node removeFeatures(IFeatureModel featureModel, Collection<String> removeFeatures) throws TimeoutException, UnkownLiteralException {
		final AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator(featureModel, removeFeatures);
		nodeCreator.setCnfType(AdvancedNodeCreator.CNFType.Regular);
		return nodeCreator.createNodes();
	}

	public static List<String> splitFeatureModel(IFeatureModel featureModel, int level, int limit) {
		final ArrayList<String> rootNames = new ArrayList<>();
		final IFeatureStructure root = featureModel.getStructure().getRoot();
		if (root != null) {
			split_rec(root, rootNames, 0, level, limit);
		}
		return rootNames;
	}

	private static void split_rec(IFeatureStructure root, ArrayList<String> rootNames, int level, int x, int y) {
		final int featureLimit = y;
		final int levelLimit = x;
		final List<IFeatureStructure> children = root.getChildren();
		for (IFeatureStructure feature : children) {
			final int c = countChildren(feature);
			if (c > 0) {
				if (c > featureLimit && level < levelLimit) {
					split_rec(feature, rootNames, level + 1, x, y);
				} else {
					rootNames.add(feature.getFeature().getName());
				}
			} else {
				rootNames.add(feature.getFeature().getName());
			}
		}
	}

	private static int countChildren(IFeatureStructure root) {
		final List<IFeatureStructure> children = root.getChildren();
		int count = children.size();
		for (IFeatureStructure feature : children) {
			count += countChildren(feature);
		}
		return count;
	}

	public static List<List<String>> mergeAtomicSets(List<List<List<Literal>>> atomicSetLists) {
		final HashMap<String, Collection<String>> atomicSetMap = new HashMap<>();
		for (List<List<Literal>> atomicSetList : atomicSetLists) {
			for (List<Literal> atomicSet : atomicSetList) {
				final HashSet<String> newSet = new HashSet<>();
				for (Literal literal : atomicSet) {
					newSet.add(literal.var.toString());
				}
				for (Literal literal : atomicSet) {
					final Collection<String> oldSet = atomicSetMap.get(literal.var.toString());
					if (oldSet != null) {
						newSet.addAll(oldSet);
					}
				}
				for (String featureName : newSet) {
					atomicSetMap.put(featureName, newSet);
				}
			}
		}
		final HashSet<Collection<String>> mergedAtomicSetsSet = new HashSet<>(atomicSetMap.values());
		final List<List<String>> mergedAtomicSets = new ArrayList<>(mergedAtomicSetsSet.size() + 1);
		for (Collection<String> atomicSet : mergedAtomicSetsSet) {
			mergedAtomicSets.add(new ArrayList<>(atomicSet));
		}
		return mergedAtomicSets;
	}
}
