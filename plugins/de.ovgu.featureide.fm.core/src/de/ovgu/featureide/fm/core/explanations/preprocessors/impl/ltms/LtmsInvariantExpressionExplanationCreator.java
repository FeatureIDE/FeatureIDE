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
package de.ovgu.featureide.fm.core.explanations.preprocessors.impl.ltms;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.Node;
import org.prop4j.Not;

import de.ovgu.featureide.fm.core.explanations.Reason;
import de.ovgu.featureide.fm.core.explanations.impl.ltms.Ltms;
import de.ovgu.featureide.fm.core.explanations.preprocessors.InvariantExpressionExplanation;
import de.ovgu.featureide.fm.core.explanations.preprocessors.InvariantExpressionExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.preprocessors.PreprocessorReason;

/**
 * Implementation of {@link InvariantExpressionExplanationCreator} using an {@link Ltms LTMS}.
 *
 * @author Timo G&uuml;nther
 */
public class LtmsInvariantExpressionExplanationCreator extends LtmsPreprocessorExplanationCreator implements InvariantExpressionExplanationCreator {

	/** Keeps track of the clause indexes of the expressions added to the solver. */
	private final List<Node> addedExpressions =
		new LinkedList<>();
	/** The amount of clauses added to the solver for the invariant expression. */
	private int invariantExpressionClauseCount;
	/** True if the expression is a tautology or false if it is a contradiction. */
	private boolean tautology;

	@Override
	public boolean isTautology() {
		return tautology;
	}

	@Override
	public void setTautology(boolean tautology) {
		this.tautology =
			tautology;
	}

	@Override
	public void setExpressionStack(Collection<Node> expressionStack) {
		super.setExpressionStack(expressionStack);
		setSubject(getExpressionStack().peek());
	}

	@Override
	public Node getSubject() {
		return (Node) super.getSubject();
	}

	@Override
	public void setSubject(Object subject) throws IllegalArgumentException {
		if ((subject != null)
			&& !(subject instanceof Node)) {
			throw new IllegalArgumentException("Illegal subject type");
		}
		super.setSubject(subject);
	}

	@Override
	protected Node createCnf() {
		final List<Node> clauses = new LinkedList<>();
		Collections.addAll(clauses, super.createCnf().getChildren());
		addedExpressions.clear();
		boolean first =
			true; // The first expression on the stack is the subject, i.e., the invariant expression.
		for (Node expression : getExpressionStack()) {
			if (first
				&& isTautology()) {
				expression =
					new Not(expression);
			}
			final Node[] expressionClauses = expression.toRegularCNF().getChildren();
			final int expressionClauseCount = expressionClauses.length;
			Collections.addAll(clauses, expressionClauses);
			for (int i =
				0; i < expressionClauseCount; i++) {
				addedExpressions.add(expression);
			}
			if (first) {
				invariantExpressionClauseCount =
					expressionClauseCount;
			}
			first =
				false;
		}
		return new And(clauses.toArray(new Node[clauses.size()]));
	}

	@Override
	public InvariantExpressionExplanation getExplanation() throws IllegalStateException {
		return getExplanation(getOracle().getExplanations());
	}

	@Override
	protected InvariantExpressionExplanation getExplanation(Collection<Set<Integer>> clauseIndexes) {
		return (InvariantExpressionExplanation) super.getExplanation(clauseIndexes);
	}

	@Override
	protected Reason getReason(int clauseIndex) {
		final int expressionIndex =
			clauseIndex
				- getTraceModel().getTraceCount();
		if (expressionIndex >= 0) {
			if (expressionIndex < invariantExpressionClauseCount) {
				return null; // Ignore clauses from the subject itself.
			}
			return new PreprocessorReason(addedExpressions.get(expressionIndex));
		}
		return super.getReason(clauseIndex);
	}

	@Override
	protected InvariantExpressionExplanation getConcreteExplanation() {
		final InvariantExpressionExplanation explanation =
			new InvariantExpressionExplanation(getSubject());
		explanation.setTautology(isTautology());
		return explanation;
	}
}
