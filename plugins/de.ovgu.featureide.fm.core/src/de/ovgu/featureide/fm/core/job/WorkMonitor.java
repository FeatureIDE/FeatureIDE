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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.job;

import de.ovgu.featureide.fm.core.job.monitor.NullMonitor;
import de.ovgu.featureide.fm.core.job.monitor.ProgressMonitor;

/**
 * Control object for {@link IJob}s. Can be used to check for cancel request, display job progress, and calling intermediate functions.
 *
 * @deprecated Use {@link NullMonitor}, {@link ProgressMonitor}, or {@link ConsoleProgressMonitor} instead.
 *
 * @author Sebastian Krieter
 * @author Marcus Pinnecke (Feature Interface)
 */
@Deprecated
public final class WorkMonitor extends AWorkMonitor {

	/**
	 * Increases the monitor's progress.
	 */
	@Override
	public void worked() {
		internalWorked();
	}

	@Override
	public boolean checkCancel() {
		return internalCheckCancel();
	}

	@Override
	public void invoke(Object t) {
		internalInvoke(t);
	}

}
