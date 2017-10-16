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
package de.ovgu.featureide.fm.core.explanations.fm.impl.ltms;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.explanations.fm.DeadFeatureExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.FalseOptionalFeatureExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanationCreatorFactory;
import de.ovgu.featureide.fm.core.explanations.fm.RedundantConstraintExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.impl.ltms.Ltms;

/**
 * Provides instances of {@link FeatureModelExplanationCreatorFactory} using an {@link Ltms LTMS}.
 *
 * @author Timo G&uuml;nther
 */
public class LtmsFeatureModelExplanationCreatorFactory extends FeatureModelExplanationCreatorFactory {

	@Override
	public DeadFeatureExplanationCreator getDeadFeatureExplanationCreator() {
		return new LtmsDeadFeatureExplanationCreator();
	}

	@Override
	public DeadFeatureExplanationCreator getDeadFeatureExplanationCreator(IFeatureModel fm) {
		return new LtmsDeadFeatureExplanationCreator(fm);
	}

	@Override
	public FalseOptionalFeatureExplanationCreator getFalseOptionalFeatureExplanationCreator() {
		return new LtmsFalseOptionalFeatureExplanationCreator();
	}

	@Override
	public FalseOptionalFeatureExplanationCreator getFalseOptionalFeatureExplanationCreator(IFeatureModel fm) {
		return new LtmsFalseOptionalFeatureExplanationCreator(fm);
	}

	@Override
	public RedundantConstraintExplanationCreator getRedundantConstraintExplanationCreator() {
		return new LtmsRedundantConstraintExplanationCreator();
	}

	@Override
	public RedundantConstraintExplanationCreator getRedundantConstraintExplanationCreator(IFeatureModel fm) {
		return new LtmsRedundantConstraintExplanationCreator(fm);
	}
}
