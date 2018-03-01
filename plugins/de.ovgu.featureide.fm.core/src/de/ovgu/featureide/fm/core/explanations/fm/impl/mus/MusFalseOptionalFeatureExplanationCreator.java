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

import org.prop4j.Literal;
import org.prop4j.solver.ContradictionException;
import org.prop4j.solver.IMusExtractor;
import org.prop4j.solver.SatSolverFactory;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.explanations.fm.FalseOptionalFeatureExplanation;
import de.ovgu.featureide.fm.core.explanations.fm.FalseOptionalFeatureExplanationCreator;

/**
 * Implementation of {@link FalseOptionalFeatureExplanationCreator} using a {@link MusExtractor MUS extractor}.
 *
 * @author Timo G&uuml;nther
 */
public class MusFalseOptionalFeatureExplanationCreator extends MusFeatureModelExplanationCreator<IFeature, FalseOptionalFeatureExplanation>
		implements FalseOptionalFeatureExplanationCreator {

	/**
	 * Constructs a new instance of this class.
	 */
	public MusFalseOptionalFeatureExplanationCreator() {
		this(null);
	}

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param solverFactory the solver factory used to create the oracle
	 */
	public MusFalseOptionalFeatureExplanationCreator(SatSolverFactory solverFactory) {
		super(solverFactory);
	}

	@Override
	public FalseOptionalFeatureExplanation getExplanation() throws IllegalStateException {
		final IMusExtractor oracle = getOracle();
		final FalseOptionalFeatureExplanation explanation;
		try {
			oracle.push(new Literal(NodeCreator.getVariable(getSubject()), false));
		} catch (final ContradictionException e1) {}
		try {
			oracle.push(new Literal(NodeCreator.getVariable(FeatureUtils.getParent(getSubject())), true));
		} catch (final ContradictionException e) {
			oracle.pop();
		}
		explanation = getExplanation(oracle.getAllMinimalUnsatisfiableSubsetIndexes());
		return explanation;
	}

	@Override
	protected FalseOptionalFeatureExplanation getConcreteExplanation() {
		return new FalseOptionalFeatureExplanation(getSubject());
	}
}
