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
package de.ovgu.featureide.fm.core.job;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.fm.core.job.util.JobFinishListener;

/**
 * Abstract eclipse job with support for {@link JobFinishListener}. This class offers convenience constructors and hides the
 * {@link #run2(IProgressMonitor)}-method.
 *
 * @deprecated Use {@link LongRunningMethod} and {@link LongRunningWrapper} instead to create jobs.
 *
 * @author Sebastian Krieter
 */
@SuppressWarnings("rawtypes")
@Deprecated
public abstract class AJob extends AbstractJob {

	public AJob(String name) {
		super(name, Job.SHORT);
	}

	public AJob(String name, int priority) {
		super(name, priority);
	}

}
