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

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.explanations.ExplanationCreator;

/**
 * Generates explanations for circumstances involving {@link IFeatureModel feature models}.
 *
 * @param <S> subject
 * @param <E> explanation
 * @author Timo G&uuml;nther
 * @see {@link DeadFeatureExplanationCreator} for explaining dead features and void feature models
 * @see {@link FalseOptionalFeatureExplanationCreator} for explaining false-optional features
 * @see {@link RedundantConstraintExplanationCreator} for explaining redundant constraints
 */
public interface FeatureModelExplanationCreator<S, E extends FeatureModelExplanation<S>> extends ExplanationCreator<S, E> {

	/**
	 * Returns the feature model context.
	 *
	 * @return the feature model context
	 */
	public IFeatureModel getFeatureModel();

	/**
	 * Sets the feature model context.
	 *
	 * @param fm the feature model context
	 */
	public void setFeatureModel(IFeatureModel fm);
}
