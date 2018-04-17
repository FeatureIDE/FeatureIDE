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
import org.prop4j.explain.solvers.SatSolverFactory;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.explanations.fm.DeadFeatureExplanation;
import de.ovgu.featureide.fm.core.explanations.fm.DeadFeatureExplanationCreator;

/**
 * Implementation of {@link DeadFeatureExplanationCreator} using a {@link MusExtractor MUS extractor}.
 *
 * @author Timo G&uuml;nther
 */
public class MusDeadFeatureExplanationCreator extends MusFeatureModelExplanationCreator<IFeature, DeadFeatureExplanation>
		implements DeadFeatureExplanationCreator {

	/**
	 * Constructs a new instance of this class.
	 */
	public MusDeadFeatureExplanationCreator() {
		this(null);
	}

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param solverFactory the solver factory used to create the oracle
	 */
	public MusDeadFeatureExplanationCreator(SatSolverFactory solverFactory) {
		super(solverFactory);
	}

	@Override
	public DeadFeatureExplanation getExplanation() throws IllegalStateException {
		final MusExtractor oracle = getOracle();
		final DeadFeatureExplanation explanation;
		oracle.push();
		try {
			oracle.addAssumption(NodeCreator.getVariable(getSubject()), true);
			explanation = getExplanation(oracle.getAllMinimalUnsatisfiableSubsetIndexes());
		} finally {
			oracle.pop();
		}
		return explanation;
	}

	@Override
	protected DeadFeatureExplanation getConcreteExplanation() {
		return new DeadFeatureExplanation(getSubject());
	}
}
