/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2020  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.explanations.fm.impl.composite;

import java.util.Collection;

import de.ovgu.featureide.fm.core.analysis.ConstraintProperties.ConstraintStatus;
import de.ovgu.featureide.fm.core.analysis.FeatureProperties.FeatureStatus;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.explanations.fm.MultipleAnomaliesExplanation;
import de.ovgu.featureide.fm.core.explanations.fm.MultipleAnomaliesExplanationCreator;

/**
 * Implements {@link MultipleAnomaliesExplanationCreator} through composition.
 *
 * @author Benedikt Jutz
 */
public class CompositeMultipleAnomaliesExplanationCreator
		extends CompositeFeatureModelExplanationCreator<IFeatureModel, MultipleAnomaliesExplanation, MultipleAnomaliesExplanationCreator>
		implements MultipleAnomaliesExplanationCreator {

	/**
	 * Constructs a new {@link CompositeMultipleAnomaliesExplanationCreator} instance.
	 *
	 * @param composites - {@link Collection}
	 */
	public CompositeMultipleAnomaliesExplanationCreator(Collection<MultipleAnomaliesExplanationCreator> composites) {
		super(composites);
	}

	/**
	 * Sets the anomaly types of the other creators.
	 *
	 * @see de.ovgu.featureide.fm.core.explanations.fm.MultipleAnomaliesExplanationCreator#setAnomalyTypes(de.ovgu.featureide.fm.core.analysis.FeatureProperties.FeatureStatus[],
	 *      de.ovgu.featureide.fm.core.analysis.ConstraintProperties.ConstraintStatus[])
	 */
	@Override
	public void setAnomalyTypes(FeatureStatus[] featureStatuses, ConstraintStatus[] constraintStatuses) {
		getComposites().forEach(creator -> creator.setAnomalyTypes(featureStatuses, constraintStatuses));
	}
}
