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

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.core.mpl.InterfaceProject;

/**
 * Abstract eclipse job which start another job when the work is finished.
 * 
 * @author Sebastian Krieter
 */
public abstract class AChainJob extends Job {
	protected InterfaceProject interfaceProject = null;
	private boolean done = false;
	
	private AChainJob nextJob = null;
	
	public AChainJob(String name) {
		this(name, Job.SHORT);
	}
	
	protected AChainJob(String name, int priority) {
		super(name);
		setPriority(priority);
	}
	
	public InterfaceProject getInterfaceProject() {
		return interfaceProject;
	}

	public void setInterfaceProject(InterfaceProject interfaceProject) {
		this.interfaceProject = interfaceProject;
		setName(getName() + " - " + interfaceProject.getProjectReference().getName());
	}
	
	public void setNextJob(AChainJob nextJob) {
		this.nextJob = nextJob;
		if (done) {
			startNextJob();
		}
	}

	@Override
	public IStatus run(IProgressMonitor monitor) {		
		final boolean ok = work();
		if (ok) {
			startNextJob();
			done = true;
			return Status.OK_STATUS;
		}
		done = true;
		return Status.CANCEL_STATUS;
	}
	
	private synchronized void startNextJob() {
		if (nextJob != null) {
			nextJob.schedule();
			nextJob = null;
		}
	}
	
	protected abstract boolean work();
}
