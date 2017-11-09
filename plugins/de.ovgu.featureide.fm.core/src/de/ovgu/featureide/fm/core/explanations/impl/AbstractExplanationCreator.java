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
package de.ovgu.featureide.fm.core.explanations.impl;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.ExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.Reason;

/**
 * Abstract implementation of {@link ExplanationCreator}.
 *
 * @param <S> subject
 * @param <E> explanation
 * @param <O> oracle
 * @author Timo G&uuml;nther
 */
public abstract class AbstractExplanationCreator<S, E extends Explanation<S>, O> implements ExplanationCreator<S, E> {

	/** The subject with an attribute to be explained. */
	private S subject;
	/** The oracle used to reason over the circumstance to explain. */
	private O oracle;

	@Override
	public S getSubject() {
		return subject;
	}

	@Override
	public void setSubject(S subject) {
		this.subject = subject;
	}

	/**
	 * Returns the oracle used to reason over the circumstance to explain.
	 *
	 * @return the oracle
	 */
	protected O getOracle() {
		if (oracle == null) {
			setOracle(createOracle());
		}
		return oracle;
	}

	/**
	 * Sets the oracle used to reason over the circumstance to explain. Creates it first if necessary.
	 *
	 * @param oracle the oracle
	 */
	protected void setOracle(O oracle) {
		this.oracle = oracle;
	}

	/**
	 * Returns a new oracle.
	 *
	 * @return a new oracle; not null
	 */
	protected abstract O createOracle();

	/**
	 * Returns an explanation for the given clauses.
	 *
	 * @param clauseIndexes indexes of clauses that serve as an explanation
	 * @return an explanation
	 */
	protected E getExplanation(Set<Integer> clauseIndexes) {
		final E explanation = getConcreteExplanation();
		for (final Integer clauseIndex : clauseIndexes) {
			final Reason<?> reason = getReason(clauseIndex);
			if (reason == null) {
				continue;
			}
			explanation.addReason(reason);
		}
		return explanation;
	}

	/**
	 * Returns the shortest explanation among the given ones. Note that this may not be the shortest one possible.
	 *
	 * @param clauseIndexes indexes of clauses of explanations to roll into one
	 * @return the shortest explanation among the given ones
	 */
	protected E getExplanation(Collection<Set<Integer>> clauseIndexes) {
		final List<E> explanations = new LinkedList<>();
		for (final Set<Integer> c : clauseIndexes) {
			explanations.add(getExplanation(c));
		}
		final E cumulatedExplanation = getConcreteExplanation();
		cumulatedExplanation.setExplanationCount(0);
		E shortestExplanation = null;
		for (final E explanation : explanations) {
			cumulatedExplanation.addExplanation(explanation); // Remember that this explanation was generated.
			if ((shortestExplanation == null) || (explanation.getReasonCount() < shortestExplanation.getReasonCount())) {
				shortestExplanation = explanation; // Remember the shortest explanation.
			}
		}
		if (shortestExplanation == null) {
			return null;
		}
		shortestExplanation.setCounts(cumulatedExplanation); // Remember the reason and explanations that were generated before.
		return shortestExplanation;
	}

	/**
	 * Returns the reason for the given clause index.
	 *
	 * @param clauseIndex index of the clause
	 * @return the reason for the given clause index
	 */
	protected abstract Reason<?> getReason(int clauseIndex);

	/**
	 * Returns a new concrete explanation.
	 *
	 * @return a new concrete explanation; not null
	 */
	protected abstract E getConcreteExplanation();
}
