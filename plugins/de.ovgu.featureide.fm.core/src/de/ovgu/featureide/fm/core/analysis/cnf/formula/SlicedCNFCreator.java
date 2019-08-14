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
package de.ovgu.featureide.fm.core.analysis.cnf.formula;

import java.util.function.Predicate;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.manipulator.remove.CNFSlicer;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;

/**
 * Creates a sliced {@link CNF}.
 *
 * @author Sebastian Krieter
 */
public abstract class SlicedCNFCreator extends ACreator<CNF> {

	private final Predicate<IFeature> filter;

	public SlicedCNFCreator(Predicate<IFeature> filter) {
		this.filter = filter;
	}

	@Override
	protected CNF create() {
		final CNFSlicer slicer = new CNFSlicer(formula.getElement(new CNFCreator()),
				Functional.mapToList(formula.getFeatureModel().getFeatures(), filter, FeatureUtils.GET_FEATURE_NAME));
		return LongRunningWrapper.runMethod(slicer);
	}

}
