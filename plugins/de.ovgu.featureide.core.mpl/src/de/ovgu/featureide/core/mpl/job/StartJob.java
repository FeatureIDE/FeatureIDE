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

import de.ovgu.featureide.core.mpl.InterfaceProject;
import de.ovgu.featureide.core.mpl.job.util.AChainJob;
import de.ovgu.featureide.core.mpl.job.util.AJobArguments;
import de.ovgu.featureide.core.mpl.job.util.IChainJob;

/**
 * Starts consecutively other jobs from a list of {@link AChainJob}s.
 * 
 * @author Sebastian Krieter
 */
public class StartJob extends AChainJob<StartJob.Arguments> {
	
	public static class Arguments extends AJobArguments {
		private final IChainJob[] jobs;
		private int index = 0;
		
		public Arguments(IChainJob[] jobs) {
			super(Arguments.class);
			this.jobs = jobs;
		}
	}
	
	protected StartJob(Arguments arguments) {
		super("", arguments);
	}
	
	@Override
	protected boolean work() {
		IChainJob curJob = arguments.jobs[arguments.index];
		InterfaceProject curInterfaceProject = curJob.getInterfaceProject();
		curInterfaceProject.loadSignaturesJob(false);
		curInterfaceProject.addJob(curJob);
		arguments.index++;
		if (arguments.index < arguments.jobs.length) {
			curInterfaceProject.addJob(new StartJob(arguments));
		}
		
		return true;
	}
}
