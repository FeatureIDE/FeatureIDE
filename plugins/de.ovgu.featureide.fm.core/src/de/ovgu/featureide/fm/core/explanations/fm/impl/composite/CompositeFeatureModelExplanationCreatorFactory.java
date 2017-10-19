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
package de.ovgu.featureide.fm.core.explanations.fm.impl.composite;

import java.util.Arrays;

import de.ovgu.featureide.fm.core.explanations.fm.DeadFeatureExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.FalseOptionalFeatureExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanationCreatorFactory;
import de.ovgu.featureide.fm.core.explanations.fm.RedundantConstraintExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.impl.ltms.LtmsFeatureModelExplanationCreatorFactory;
import de.ovgu.featureide.fm.core.explanations.fm.impl.mus.MusFeatureModelExplanationCreatorFactory;

/**
 * Provides instances of {@link FeatureModelExplanationCreator} using composition.
 *
 * @author Timo G&uuml;nther
 */
public class CompositeFeatureModelExplanationCreatorFactory extends FeatureModelExplanationCreatorFactory {

	/** Factory for LTMS. */
	private final FeatureModelExplanationCreatorFactory ltms = new LtmsFeatureModelExplanationCreatorFactory();
	/** Factory for MUS. */
	private final FeatureModelExplanationCreatorFactory mus = new MusFeatureModelExplanationCreatorFactory();

	@Override
	public DeadFeatureExplanationCreator getDeadFeatureExplanationCreator() {
		return new CompositeDeadFeatureExplanationCreator(Arrays.asList(ltms.getDeadFeatureExplanationCreator(), mus.getDeadFeatureExplanationCreator()));
	}

	@Override
	public FalseOptionalFeatureExplanationCreator getFalseOptionalFeatureExplanationCreator() {
		return new CompositeFalseOptionalFeatureExplanationCreator(
				Arrays.asList(ltms.getFalseOptionalFeatureExplanationCreator(), mus.getFalseOptionalFeatureExplanationCreator()));
	}

	@Override
	public RedundantConstraintExplanationCreator getRedundantConstraintExplanationCreator() {
		return new CompositeRedundantConstraintExplanationCreator(
				Arrays.asList(ltms.getRedundantConstraintExplanationCreator(), mus.getRedundantConstraintExplanationCreator()));
	}
}
