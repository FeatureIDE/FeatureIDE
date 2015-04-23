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

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.nio.charset.Charset;
import java.util.Collection;
import java.util.List;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.osgi.framework.BundleContext;

import de.ovgu.featureide.fm.core.ExtendedFeatureModel.UsedModel;
import de.ovgu.featureide.fm.core.io.AbstractFeatureModelReader;
import de.ovgu.featureide.fm.core.io.ModelIOFactory;
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
	 * 	Returns {@code null} if {@code projects} is empty.
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
		logInfo("Reading Model File...");
		final IContainer outputDir = file.getParent();
		if (outputDir == null || !(outputDir instanceof IFolder)) {
			return;
		}

		final int modelType = ModelIOFactory.getTypeByFileName(file.getName());
		if (modelType == ModelIOFactory.TYPE_UNKNOWN) {
			return;
		}
		final FeatureModel fm = ModelIOFactory.getNewFeatureModel(modelType);
		final AbstractFeatureModelReader reader = ModelIOFactory.getModelReader(fm, modelType);

		try {
			reader.readFromFile(file.getLocation().toFile());
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

			final List<List<Feature>> unnomralFeature = fma.analyzeFeatures();

			Collection<Feature> analyzedFeatures = unnomralFeature.get(0);
			sb.append("Core Features (");
			sb.append(analyzedFeatures.size());
			sb.append("): ");
			for (Feature coreFeature : analyzedFeatures) {
				sb.append(coreFeature.getName());
				sb.append(", ");
			}
			analyzedFeatures = unnomralFeature.get(1);
			sb.append("\nDead Features (");
			sb.append(analyzedFeatures.size());
			sb.append("): ");
			for (Feature deadFeature : analyzedFeatures) {
				sb.append(deadFeature.getName());
				sb.append(", ");
			}
			analyzedFeatures = fma.getFalseOptionalFeatures();
			sb.append("\nFO Features (");
			sb.append(analyzedFeatures.size());
			sb.append("): ");
			for (Feature foFeature : analyzedFeatures) {
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
			logInfo("Printed Output File.");
		} catch (Exception e) {
			logError(e);
		}
	}
}
