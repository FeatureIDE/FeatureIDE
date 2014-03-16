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

/**
 * Starts consecutively other jobs from a list of {@link AChainJob}s.
 * 
 * @author Sebastian Krieter
 */
public class StartJob extends AChainJob {
	
	private final AChainJob[] jobs;
	private final int index;
	
	public StartJob(AChainJob[] jobs) {
		this(jobs, 0);
	}
	
	public StartJob(AChainJob[] jobs, int index) {
		super("");
		this.jobs = jobs;
		this.index = index;
	}
	
	@Override
	protected boolean work() {
		AChainJob curJob = jobs[index];
		InterfaceProject curInterfaceProject = curJob.getInterfaceProject();
		curInterfaceProject.loadSignaturesJob(false);
		curInterfaceProject.addJob(curJob);
		if (index < jobs.length - 1) {
			curInterfaceProject.addJob(new StartJob(jobs, index + 1));
		}
		
		return true;
	}
}