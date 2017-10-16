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
package de.ovgu.featureide.fm.core.explanations.fm.impl.mus;

import org.prop4j.explain.solvers.MusExtractor;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.explanations.fm.DeadFeatureExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.FalseOptionalFeatureExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanationCreatorFactory;
import de.ovgu.featureide.fm.core.explanations.fm.RedundantConstraintExplanationCreator;

/**
 * Provides instances of {@link FeatureModelExplanationCreator} using a {@link MusExtractor MUS extractor}.
 *
 * @author Timo G&uuml;nther
 */
public class MusFeatureModelExplanationCreatorFactory extends FeatureModelExplanationCreatorFactory {

	@Override
	public DeadFeatureExplanationCreator getDeadFeatureExplanationCreator() {
		return new MusDeadFeatureExplanationCreator();
	}

	@Override
	public DeadFeatureExplanationCreator getDeadFeatureExplanationCreator(IFeatureModel fm) {
		return new MusDeadFeatureExplanationCreator(fm);
	}

	@Override
	public FalseOptionalFeatureExplanationCreator getFalseOptionalFeatureExplanationCreator() {
		return new MusFalseOptionalFeatureExplanationCreator();
	}

	@Override
	public FalseOptionalFeatureExplanationCreator getFalseOptionalFeatureExplanationCreator(IFeatureModel fm) {
		return new MusFalseOptionalFeatureExplanationCreator(fm);
	}

	@Override
	public RedundantConstraintExplanationCreator getRedundantConstraintExplanationCreator() {
		return new MusRedundantConstraintExplanationCreator();
	}

	@Override
	public RedundantConstraintExplanationCreator getRedundantConstraintExplanationCreator(IFeatureModel fm) {
		return new MusRedundantConstraintExplanationCreator(fm);
	}
}
