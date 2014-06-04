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
package de.ovgu.featureide.core.mpl.job.util;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.core.mpl.InterfaceProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.job.util.AJobArguments;

/**
 * Abstract eclipse job which start another job when the work is finished.
 * 
 * @author Sebastian Krieter
 */
public abstract class AChainJob<T extends AJobArguments> extends Job implements IChainJob {
	
	protected InterfaceProject interfaceProject = null;
	protected final T arguments;
	
	private Boolean done = false;
	private IChainJob nextJob = null;
	
	protected AChainJob(String name, T arguments) {
		this(name, Job.SHORT, arguments);
	}
	
	protected AChainJob(String name, int priority, T arguments) {
		super(name);
		setPriority(priority);
		this.arguments = arguments;
	}
	
	public InterfaceProject getInterfaceProject() {
		return interfaceProject;
	}

	public void setInterfaceProject(InterfaceProject interfaceProject) {
		this.interfaceProject = interfaceProject;
		setName(getName() + " - " + interfaceProject.getProjectReference().getName());
	}
	
	public void setNextJob(IChainJob nextJob) {
		this.nextJob = nextJob;
		synchronized (done) {
			if (done) {
				startNextJob();
			}
		}
	}

	@Override
	public IStatus run(IProgressMonitor monitor) {
		boolean ok = false;
		try {
			ok = work();
		} catch (Exception e) {
			MPLPlugin.getDefault().logError(e);
		}
		
		synchronized (done) {
			done = true;
		}
		if (ok) {
			startNextJob();
			return Status.OK_STATUS;
		}
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
