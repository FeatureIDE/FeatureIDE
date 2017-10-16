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
import de.ovgu.featureide.fm.core.explanations.ExplanationCreatorFactory;
import de.ovgu.featureide.fm.core.explanations.fm.impl.mus.MusFeatureModelExplanationCreatorFactory;

/**
 * Provides instances of {@link FeatureModelExplanationCreator}.
 *
 * @author Timo G&uuml;nther
 */
public abstract class FeatureModelExplanationCreatorFactory implements ExplanationCreatorFactory {

	/**
	 * Returns a default instance of this class.
	 *
	 * @return a default instance of this class
	 */
	public static FeatureModelExplanationCreatorFactory getDefault() {
		return new MusFeatureModelExplanationCreatorFactory();
	}

	/**
	 * Returns an instance of {@link DeadFeatureExplanationCreator}.
	 *
	 * @return an instance of {@link DeadFeatureExplanationCreator}
	 */
	public abstract DeadFeatureExplanationCreator getDeadFeatureExplanationCreator();

	/**
	 * Returns an instance of {@link DeadFeatureExplanationCreator}.
	 *
	 * @param fm the feature model context
	 * @return an instance of {@link DeadFeatureExplanationCreator}
	 */
	public abstract DeadFeatureExplanationCreator getDeadFeatureExplanationCreator(IFeatureModel fm);

	/**
	 * Returns an instance of {@link FalseOptionalFeatureExplanationCreator}.
	 *
	 * @return an instance of {@link FalseOptionalFeatureExplanationCreator}
	 */
	public abstract FalseOptionalFeatureExplanationCreator getFalseOptionalFeatureExplanationCreator();

	/**
	 * Returns an instance of {@link FalseOptionalFeatureExplanationCreator}.
	 *
	 * @param fm the feature model context
	 * @return an instance of {@link FalseOptionalFeatureExplanationCreator}
	 */
	public abstract FalseOptionalFeatureExplanationCreator getFalseOptionalFeatureExplanationCreator(IFeatureModel fm);

	/**
	 * Returns an instance of {@link RedundantConstraintExplanationCreator}.
	 *
	 * @return an instance of {@link RedundantConstraintExplanationCreator}
	 */
	public abstract RedundantConstraintExplanationCreator getRedundantConstraintExplanationCreator();

	/**
	 * Returns an instance of {@link RedundantConstraintExplanationCreator}.
	 *
	 * @param fm the feature model context
	 * @return an instance of {@link RedundantConstraintExplanationCreator}
	 */
	public abstract RedundantConstraintExplanationCreator getRedundantConstraintExplanationCreator(IFeatureModel fm);
}
