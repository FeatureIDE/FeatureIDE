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
package de.ovgu.featureide.fm.ui.editors.featuremodel.figures;

import org.eclipse.draw2d.Figure;

import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelReason;

/**
 * A figure for feature model elements, meaning features and constraints.
 *
 * @author Timo G&uuml;nther
 */
public abstract class ModelElementFigure extends Figure {

	/** the currently active reason */
	private FeatureModelReason activeReason;

	/**
	 * Sets the currently active reason.
	 *
	 * @param activeReason new active reason; null to reset
	 */
	public void setActiveReason(FeatureModelReason activeReason) {
		this.activeReason = activeReason;
	}

	/**
	 * Returns the currently active reason.
	 *
	 * @return the currently active reason
	 */
	public FeatureModelReason getActiveReason() {
		return activeReason;
	}
}
