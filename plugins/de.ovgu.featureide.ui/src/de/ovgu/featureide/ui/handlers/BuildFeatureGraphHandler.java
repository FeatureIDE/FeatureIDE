/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.handlers;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.LinkedList;

import org.prop4j.analyses.FGBuilder;
import org.prop4j.solver.SatInstance;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.conf.IFeatureGraph;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.io.FeatureGraphFormat;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;
import de.ovgu.featureide.fm.core.job.IJob;
import de.ovgu.featureide.fm.core.job.IRunner;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.util.JobFinishListener;
import de.ovgu.featureide.ui.handlers.base.AFeatureProjectHandler;

public class BuildFeatureGraphHandler extends AFeatureProjectHandler {

	private final LinkedList<IFeatureProject> projectList = new LinkedList<>();

	@Override
	protected void singleAction(IFeatureProject project) {
		projectList.add(project);
	}

	@Override
	protected void endAction() {
		for (final IFeatureProject project : projectList) {
			final Path path = Paths.get(project.getProject().getFile("model.fg").getLocationURI());
			final IFeatureModel fm = project.getFeatureModel();
			final SatInstance sat =
				new SatInstance(AdvancedNodeCreator.createRegularCNF(fm), Functional.mapToList(fm.getFeatures(), FeatureUtils.GET_FEATURE_NAME));
			final IRunner<IFeatureGraph> runner = LongRunningWrapper.getRunner(new FGBuilder(sat));
			runner.addJobFinishedListener(new JobFinishListener<IFeatureGraph>() {

				@Override
				public void jobFinished(IJob<IFeatureGraph> finishedJob) {
					SimpleFileHandler.save(path, finishedJob.getResults(), new FeatureGraphFormat());
				}
			});
			runner.schedule();
		}
		projectList.clear();
	}

}
