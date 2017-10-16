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
package de.ovgu.featureide.fm.core.explanations.fm;

import de.ovgu.featureide.fm.core.base.IFeature;

/**
 * Generates explanations for dead features in feature models. Also supports explanations for void feature models by explaining why the root feature is dead.
 *
 * @author Timo G&uuml;nther
 */
public interface DeadFeatureExplanationCreator extends FeatureModelExplanationCreator {

	/**
	 * Returns the dead feature in the feature model.
	 *
	 * @return the dead feature in the feature model
	 */
	public IFeature getDeadFeature();

	/**
	 * Sets the dead feature in the feature model.
	 *
	 * @param deadFeature the dead feature in the feature model
	 */
	public void setDeadFeature(IFeature deadFeature);

	/**
	 * Returns an explanation why the specified feature of the specified feature model is dead. A dead root feature also means a void feature model.
	 */
	@Override
	public DeadFeatureExplanation getExplanation() throws IllegalStateException;
}
