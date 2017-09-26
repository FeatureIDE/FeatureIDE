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
package de.ovgu.featureide.fm.core.base;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.FMPoint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.functional.Functional.IFunction;

/**
 * @deprecated For legacy purposes only.
 *
 * @author Marcus Pinnecke
 */
@Deprecated
public final class FeatureUtilsLegacy {

	public static final IFunction<Constraint, IConstraint> CONSTRAINT_TO_ICONSTRANT = new IFunction<Constraint, IConstraint>() {

		@Override
		public IConstraint invoke(Constraint t) {
			FeatureUtils.requireNonNull(t);

			return convert(t);
		};
	};

	public static final IFunction<Feature, IFeature> FEATURE_TO_IFEATURE = new IFunction<Feature, IFeature>() {

		@Override
		public IFeature invoke(Feature t) {
			FeatureUtils.requireNonNull(t);

			return convert(t);
		};
	};

	public static final IFunction<IConstraint, Constraint> ICONSTRAINT_TO_CONSTRANT = new IFunction<IConstraint, Constraint>() {

		@Override
		public Constraint invoke(IConstraint t) {
			FeatureUtils.requireNonNull(t);

			return convert(t);
		};
	};

	public static final IFunction<IFeature, Feature> IFEATURE_TO_FEATURE = new IFunction<IFeature, Feature>() {

		@Override
		public Feature invoke(IFeature t) {
			FeatureUtils.requireNonNull(t);

			return convert(t);
		};
	};

	public static final IConstraint convert(Constraint c) {
		FeatureUtils.requireNonNull(c);

		return c.constraint;
	}

	public static final IFeature convert(Feature f) {
		FeatureUtils.requireNonNull(f);

		return f.feature;
	}

	public static final IFeatureModel convert(FeatureModel fm) {
		FeatureUtils.requireNonNull(fm);

		return fm.model;
	}

	public static final Constraint convert(IConstraint c) {
		FeatureUtils.requireNonNull(c);

		return new Constraint(c);
	}

	public static final Feature convert(IFeature f) {
		FeatureUtils.requireNonNull(f);

		return new Feature(f);
	}

	public static final FeatureModel convert(IFeatureModel fm) {
		FeatureUtils.requireNonNull(fm);

		return new FeatureModel(fm);
	}

	public static final FMPoint getLocation(IConstraint constraint) {
		return null;
	}

	public static final FMPoint getLocation(IFeature feature) {
		return null;
	}

	public static final void setLocation(IConstraint constraint, FMPoint newLocation) {}

	public static final void setNewLocation(IFeature feature, FMPoint newLocation) {}

	private FeatureUtilsLegacy() {}

}
