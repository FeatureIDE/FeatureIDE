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
package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * Parent for the actual {@link ConfigNode}s.
 *
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public class StatisticsSemanticalFeatureModel extends LazyParent {

	private final IFeatureModel model;

	public StatisticsSemanticalFeatureModel(String description, IFeatureModel model) {
		super(description);
		this.model = model;
	}

	@Override
	protected void initChildren() {
		// Cached validity for speed
		final boolean isValid = model.getAnalyser().valid();

		addChild(new Parent(MODEL_VOID, isValid));

		addChild(new CoreFeaturesParentNode(CORE_FEATURES, model));

		addChild(new DeadFeaturesParentNode(DEAD_FEATURES, model));

		addChild(new FalseOptionalFeaturesParentNode(FO_FEATURES, model));

		addChild(new AtomicParentNode(ATOMIC_SETS, model));

		addChild(new ConfigNode(DESC_CONFIGS, model));

		addChild(new ConfigNode(DESC_VARIANTS, model));
	}
}
