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
package de.ovgu.featureide.fm.core.configuration;

import java.util.List;

import org.prop4j.Node;
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

	boolean isLoaded();

	LongRunningMethod<Void> resolve();

	/**
	 * Ignores hidden features. Use this, when propgate is disabled (hidden features are not updated).
	 */
	LongRunningMethod<Boolean> isValidNoHidden();

	LongRunningMethod<Boolean> canBeValid();

	LongRunningMethod<Void> load();

	LongRunningMethod<Void> leadToValidConfiguration(List<SelectableFeature> featureList);

	LongRunningMethod<Void> leadToValidConfiguration(List<SelectableFeature> featureList, int mode);

	/**
	 * Counts the number of possible solutions.
	 *
	 * @return a positive value equal to the number of solutions (if the method terminated in time)</br> or a negative value (if a timeout occurred) that
	 *         indicates that there are more solutions than the absolute value
	 */
	LongRunningMethod<Long> number(long timeout, boolean includeHiddenFeatures);

	LongRunningMethod<Void> update(boolean redundantManual, List<SelectableFeature> featureOrder);

	LongRunningMethod<Void> update(boolean redundantManual);

	LongRunningMethod<Void> update();

	LongRunningMethod<List<Node>> findOpenClauses(List<SelectableFeature> featureList);

}
