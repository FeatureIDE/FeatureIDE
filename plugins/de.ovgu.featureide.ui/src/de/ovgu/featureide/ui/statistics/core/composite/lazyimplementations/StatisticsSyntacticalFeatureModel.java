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

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * Counts and categorizes features in the given feature model.
 *
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public final class StatisticsSyntacticalFeatureModel extends LazyParent {

	private static final double precision = 1000.0;

	private final IFeatureModel model;

	public StatisticsSyntacticalFeatureModel(String description, IFeatureModel model) {
		super(description, null);
		this.model = model;
	}

	@Override
	protected void initChildren() {
		if (model != null) {

			final int constraints = model.getConstraintCount();

			final Collection<IFeature> listOfFeatures = Functional.toList(model.getFeatures());

			final List<IFeature> listOfCompoundFeatures = new ArrayList<IFeature>();
			final List<IFeature> listOfPrimitiveFeatures = new ArrayList<IFeature>();
			final List<IFeature> listOfAbstractFeatures = new ArrayList<IFeature>();
			final List<IFeature> listOfConcreteFeatures = new ArrayList<IFeature>();

			for (final IFeature f : listOfFeatures) {
				if (f.getStructure().getChildren().isEmpty()) {
					listOfPrimitiveFeatures.add(f);
				} else {
					listOfCompoundFeatures.add(f);
				}
				if (f.getStructure().isConcrete()) {
					listOfConcreteFeatures.add(f);
				} else {
					listOfAbstractFeatures.add(f);
				}
			}

			final HashSet<IFeature> constraintFeatures = new HashSet<>(model.getNumberOfFeatures() << 1);
			for (final IConstraint constraint : model.getConstraints()) {
				constraintFeatures.addAll(constraint.getContainedFeatures());
			}

			addChild(new FeatureListNode(NUMBER_FEATURES, listOfFeatures));

			addChild(new FeatureListNode(NUMBER_CONCRETE, listOfConcreteFeatures));

			addChild(new FeatureListNode(NUMBER_ABSTRACT, listOfAbstractFeatures));

			addChild(new FeatureListNode(NUMBER_COMPOUND, listOfCompoundFeatures));

			addChild(new FeatureListNode(NUMBER_TERMINAL, listOfPrimitiveFeatures));

			addChild(new FeatureListNode(NUMBER_HIDDEN, model.getAnalyser().getHiddenFeatures()));

			addChild(new Parent(NUMBER_CONSTRAINTS, constraints));

			addChild(new Parent(NUMBER_CONSTRAINT_FEATURES, constraintFeatures.size()));

			addChild(new Parent(CONSTRAINT_RATIO, Math.floor((precision * constraintFeatures.size()) / model.getNumberOfFeatures()) / precision));

		}
	}
}
