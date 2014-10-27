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
package de.ovgu.featureide.fm.core.job;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.fm.core.job.util.JobArguments;

/**
 * Abstract eclipse job for a project.
 * 
 * @author Sebastian Krieter
 */
public abstract class AProjectJob<T extends JobArguments> extends AStoppableJob implements IProjectJob {
	
	protected IProject project = null;
	protected final T arguments;
	
	protected AProjectJob(String name, int priority, T arguments) {
		super(name, priority);
		this.arguments = arguments;
	}
	
	protected AProjectJob(String name, T arguments) {
		this(name, Job.SHORT, arguments);
	}

	@Override
	public final IProject getProject() {
		return project;
	}

	@Override
	public final void setProject(IProject project) {
		this.project = project;
		setName(getName() + " - " + project.getName());
	}
}
