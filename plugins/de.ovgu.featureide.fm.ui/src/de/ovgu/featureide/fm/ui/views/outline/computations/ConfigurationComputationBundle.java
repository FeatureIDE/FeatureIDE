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
package de.ovgu.featureide.fm.ui.views.outline.computations;

import java.util.ArrayList;
import java.util.List;

import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.ui.views.outline.computations.impl.ManuallySelectedFeatureCountComputation;
import de.ovgu.featureide.fm.ui.views.outline.computations.impl.ManuallyUnselectedFeatureCountComputation;
import de.ovgu.featureide.fm.ui.views.outline.computations.impl.SelectedFeatureCountComputation;
import de.ovgu.featureide.fm.ui.views.outline.computations.impl.UndecidedFeatureCountComputation;
import de.ovgu.featureide.fm.ui.views.outline.computations.impl.UnselectedFeatureCountComputation;

/**
 * TODO description
 *
 * @author Chico Sundermann
 */
public class ConfigurationComputationBundle {
	List<IConfigurationComputation> computations;

	public void initComputations(Configuration config) {
		computations = new ArrayList<IConfigurationComputation>();
		computations.add(new SelectedFeatureCountComputation(config));
		computations.add(new ManuallySelectedFeatureCountComputation(config));
		computations.add(new UnselectedFeatureCountComputation(config));
		computations.add(new ManuallyUnselectedFeatureCountComputation(config));
		computations.add(new UndecidedFeatureCountComputation(config));
	}

	public List<ComputationHeader> getComputationHeaders() {
		final List<ComputationHeader> headers = new ArrayList<ComputationHeader>();
		for (final IConfigurationComputation comp : computations) {
			headers.add(new ComputationHeader(comp));
		}
		return headers;
	}
}
