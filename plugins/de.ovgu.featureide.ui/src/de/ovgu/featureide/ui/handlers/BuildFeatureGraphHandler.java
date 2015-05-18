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
package de.ovgu.featureide.ui.handlers;

import java.util.LinkedList;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.conf.CreateFeatureGraphJob;
import de.ovgu.featureide.fm.core.conf.FeatureGraphStatisticJob;
import de.ovgu.featureide.fm.core.job.IProjectJob;
import de.ovgu.featureide.fm.core.job.util.JobSequence;
import de.ovgu.featureide.ui.handlers.base.AFeatureProjectHandler;

public class BuildFeatureGraphHandler extends AFeatureProjectHandler {

	private final LinkedList<IFeatureProject> projectList = new LinkedList<>();
	
	@Override
	protected void singleAction(IFeatureProject project) {
		projectList.add(project);
	}
	
	@Override
	protected void endAction() {
		final JobSequence global = new JobSequence();
		for (IFeatureProject project : projectList) {
			final JobSequence j = new JobSequence();
			final IProjectJob newJob1 = new CreateFeatureGraphJob.Arguments(project.getFeatureModel()).createJob();
			final IProjectJob newJob2 = new FeatureGraphStatisticJob.Arguments(project.getFeatureModel()).createJob();
			newJob1.setProject(project.getProject());
			newJob2.setProject(project.getProject());
			j.addJob(newJob1);
			j.addJob(newJob2);
			global.addJob(j);
		}
		global.schedule();
	}

}
