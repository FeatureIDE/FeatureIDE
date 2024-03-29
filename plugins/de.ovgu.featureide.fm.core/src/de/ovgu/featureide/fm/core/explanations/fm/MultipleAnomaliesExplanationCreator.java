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
package de.ovgu.featureide.fm.core.explanations.fm;

import de.ovgu.featureide.fm.core.analysis.ConstraintProperties.ConstraintStatus;
import de.ovgu.featureide.fm.core.analysis.FeatureProperties.FeatureStatus;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * {@link MultipleAnomaliesExplanationCreator} provides an interface for creators of {@link MultipleAnomaliesExplanation}s.
 *
 * @author Benedikt Jutz
 */
public interface MultipleAnomaliesExplanationCreator extends FeatureModelExplanationCreator<IFeatureModel, MultipleAnomaliesExplanation> {

	/**
	 * Configures the anomaly types to find explanations for.
	 *
	 * @param featureStatuses - {@link FeatureStatus}[]
	 * @param constraintStatuses - {@link ConstraintStatus}[]
	 */
	void setAnomalyTypes(FeatureStatus[] featureStatuses, ConstraintStatus[] constraintStatuses);
}
