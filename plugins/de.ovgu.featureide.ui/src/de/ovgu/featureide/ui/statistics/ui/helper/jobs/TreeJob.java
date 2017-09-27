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
package de.ovgu.featureide.ui.statistics.ui.helper.jobs;

import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * Job for the {@code FeatureStatisticsView}. <p> Behaves like a normal {@link Job} but stores a {@link Parent} for the calculation.
 *
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public abstract class TreeJob implements LongRunningMethod<Boolean>, ITreeJob {

	protected Parent calculated;

	public TreeJob(Parent calculated) {
		this.calculated = calculated;
	}

	@Override
	public Parent getCalculated() {
		return calculated;
	}

	@Override
	public void setCalculated(Parent calculated) {
		this.calculated = calculated;
	}

}
