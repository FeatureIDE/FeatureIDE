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

import java.util.LinkedList;

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.core.mpl.job.util.AChainJob;
import de.ovgu.featureide.core.mpl.job.util.AJobArguments;
import de.ovgu.featureide.core.mpl.job.util.IChainJob;
import de.ovgu.featureide.core.mpl.job.util.JobManager;

/**
 * Starts consecutively other jobs from a list of {@link AChainJob}s.
 * 
 * @author Sebastian Krieter
 */
public class StartJob extends AChainJob<StartJob.Arguments> {

	public static class Arguments extends AJobArguments {
		private final LinkedList<IChainJob> jobs;

		public Arguments(LinkedList<IChainJob> jobs) {
			super(Arguments.class);
			this.jobs = jobs;
		}
	}

	protected StartJob(Arguments arguments) {
		super("", arguments);
	}

	@Override
	protected boolean work() {
		IChainJob curJob = arguments.jobs.removeFirst();
		IProject curProject = curJob.getProject();
		JobManager.addJob(curProject, curJob);
		if (!arguments.jobs.isEmpty()) {
			JobManager.addJob(curProject, new StartJob(arguments));
		}
		return true;
	}
}
