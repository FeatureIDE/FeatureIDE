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
package de.ovgu.featureide.fm.core.explanations.preprocessors.impl.mus;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.explain.solvers.MusExtractor;
import org.prop4j.explain.solvers.SatSolverFactory;

import de.ovgu.featureide.fm.core.explanations.Reason;
import de.ovgu.featureide.fm.core.explanations.preprocessors.InvariantPresenceConditionExplanation;
import de.ovgu.featureide.fm.core.explanations.preprocessors.InvariantPresenceConditionExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.preprocessors.PreprocessorReason;

/**
 * Implementation of {@link InvariantPresenceConditionExplanationCreator} using a {@link MusExtractor MUS extractor}.
 *
 * @author Timo G&uuml;nther
 */
public class MusInvariantPresenceConditionExplanationCreator extends MusPreprocessorExplanationCreator<Node, InvariantPresenceConditionExplanation>
		implements InvariantPresenceConditionExplanationCreator {

	/** Keeps track of the clause indexes of the expressions added to the solver. */
	private final List<Node> expressionClauses = new ArrayList<>();
	/** The amount of clauses added to the solver for the invariant expression. */
	private int invariantExpressionClauseCount;
	/** True if the expression is a tautology or false if it is a contradiction. */
	private boolean tautology;

	/**
	 * Constructs a new instance of this class.
	 */
	public MusInvariantPresenceConditionExplanationCreator() {
		this(null);
	}

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param solverFactory the solver factory used to create the oracle
	 */
	public MusInvariantPresenceConditionExplanationCreator(SatSolverFactory solverFactory) {
		super(solverFactory);
	}

	@Override
	public boolean isTautology() {
		return tautology;
	}

	@Override
	public void setTautology(boolean tautology) {
		this.tautology = tautology;
	}

	@Override
	public void setExpressionStack(Collection<Node> expressionStack) {
		super.setExpressionStack(expressionStack);
		setSubject(getExpressionStack().peek());
	}

	@Override
	public InvariantPresenceConditionExplanation getExplanation() throws IllegalStateException {
		final MusExtractor oracle = getOracle();
		final InvariantPresenceConditionExplanation explanation;
		oracle.push();
		try {
			expressionClauses.clear();
			boolean first = true; // The first expression on the stack is the subject, i.e., the invariant expression.
			for (Node expression : getExpressionStack()) {
				if (first && isTautology()) {
					expression = new Not(expression);
				}
				final int expressionClauseCount = oracle.addFormula(expression);
				for (int i = 0; i < expressionClauseCount; i++) {
					expressionClauses.add(expression);
				}
				if (first) {
					invariantExpressionClauseCount = expressionClauseCount;
				}
				first = false;
			}
			explanation = getExplanation(oracle.getAllMinimalUnsatisfiableSubsetIndexes());
		} finally {
			oracle.pop();
		}
		return explanation;
	}

	@Override
	protected Reason<?> getReason(int clauseIndex) {
		final int expressionIndex = clauseIndex - getTraceModel().getTraceCount();
		if (expressionIndex >= 0) {
			if (expressionIndex < invariantExpressionClauseCount) {
				return null; // Ignore clauses from the subject itself.
			}
			return new PreprocessorReason(expressionClauses.get(expressionIndex));
		}
		return super.getReason(clauseIndex);
	}

	@Override
	protected InvariantPresenceConditionExplanation getConcreteExplanation() {
		final InvariantPresenceConditionExplanation explanation = new InvariantPresenceConditionExplanation(getSubject());
		explanation.setTautology(isTautology());
		return explanation;
	}
}
