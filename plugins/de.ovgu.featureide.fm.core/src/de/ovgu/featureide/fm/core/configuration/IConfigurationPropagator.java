/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.configuration;

import java.util.Collection;
import java.util.List;

import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.job.LongRunningMethod;

/**
 * Interface for a configuration propagator.
 *
 * @author Sebastian Krieter
 */

public interface IConfigurationPropagator {

	LongRunningMethod<List<List<String>>> getSolutions(int max) throws TimeoutException;

	/**
	 * Checks that all manual and automatic selections are valid.<br> Abstract features will <b>not</b> be ignored.
	 *
	 * @return {@code true} if the current selection is a valid configuration
	 */
	LongRunningMethod<Boolean> isValid();

	/**
	 * Ignores hidden features. Use this, when propgate is disabled (hidden features are not updated).
	 */
	LongRunningMethod<Boolean> isValidNoHidden();

	LongRunningMethod<Boolean> canBeValid();

	/**
	 * Counts the number of possible solutions.
	 *
	 * @return a positive value equal to the number of solutions (if the method terminated in time)<br> or a negative value (if a timeout occurred) that
	 *         indicates that there are more solutions than the absolute value
	 */
	LongRunningMethod<Long> number(int timeout);

	LongRunningMethod<Collection<SelectableFeature>> update(boolean redundantManual, List<SelectableFeature> featureOrder);

	LongRunningMethod<Collection<SelectableFeature>> update(boolean redundantManual);

	LongRunningMethod<Collection<SelectableFeature>> update();

	LongRunningMethod<Collection<SelectableFeature>> resetAutomatic();

	LongRunningMethod<Boolean> completeRandomly();

	LongRunningMethod<Boolean> completeMin();

	LongRunningMethod<Boolean> completeMax();

	LongRunningMethod<Collection<SelectableFeature>> resolve();

	LongRunningMethod<List<List<String>>> coverFeatures(Collection<String> features, boolean selection);

	/**
	 * Returns a subset of clauses from the feature model that are currently unsatisfied and marks all contained {@link SelectableFeature features} (see
	 * {@link SelectableFeature#getRecommended()} and {@link SelectableFeature#getOpenClauses()}). Features that are undefined are considered deselected.
	 *
	 *
	 * @return A list of unsatisfied clauses.
	 */
	LongRunningMethod<Collection<SelectableFeature>> findOpenClauses();

	boolean isIncludeAbstractFeatures();

	void setIncludeAbstractFeatures(boolean includeAbstractFeatures);

}
