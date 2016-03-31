/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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

import de.ovgu.featureide.fm.core.job.AStoppableJob;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * A internal job for the statistics view.
 * 
 * @author Dominik Hamann
 */
public abstract class StoppableTreeJob extends AStoppableJob  implements ITreeJob {

	public StoppableTreeJob(String name, Parent calculated) {
		super(name);
		this.calculated = calculated;
	}

	protected Parent calculated;
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.statistics.ui.helper.ITreeJob#getCalculated()
	 */
	@Override
	public Parent getCalculated() {
		return calculated;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.statistics.ui.helper.ITreeJob#setCalculated()
	 */
	@Override
	public void setCalculated(Parent calculated) {
	this.calculated = calculated;
	}



}
