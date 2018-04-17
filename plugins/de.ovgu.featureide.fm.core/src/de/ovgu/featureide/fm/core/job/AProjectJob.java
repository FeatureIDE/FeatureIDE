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

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.util.JobArguments;

/**
 * This class implements support for Eclipse jobs. The {@link JobArguments} object should be extended to add constructor parameters, and can be used to
 * conveniently start several {@link AProjectJob}s.
 *
 * @author Sebastian Krieter
 */
public abstract class AProjectJob<T extends JobArguments, R> implements LongRunningMethod<R> {

	protected final T arguments;

	protected IMonitor workMonitor;

	protected AProjectJob(T arguments) {
		this.arguments = arguments;
	}

	protected AProjectJob(String name, T arguments) {
		this.arguments = arguments;
	}

}
