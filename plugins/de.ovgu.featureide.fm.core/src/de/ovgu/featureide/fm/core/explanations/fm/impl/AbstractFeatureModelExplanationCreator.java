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
package de.ovgu.featureide.fm.core.explanations.fm.impl;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;
import de.ovgu.featureide.fm.core.editing.FeatureModelToNodeTraceModel;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.Reason;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelReason;

/**
 * Abstract implementation of {@link FeatureModelExplanationCreator}.
 *
 * @author Timo G&uuml;nther
 */
public abstract class AbstractFeatureModelExplanationCreator implements FeatureModelExplanationCreator {

	/** The subject with an attribute to be explained. */
	private Object subject;
	/** The feature model context. */
	private IFeatureModel fm;
	/**
	 * Creates the CNF from the feature model. Created and reset together with the feature model.
	 */
	private AdvancedNodeCreator nodeCreator;
	/**
	 * A formula representation of the feature model in CNF (conjunctive normal form). The CNF is created lazily when needed and reset when the feature model
	 * changes. This makes it possible to reuse the CNF for different defects of the same type in the same feature model.
	 */
	private Node cnf;
	/**
	 * The trace model. Created and reset together with the CNF.
	 */
	private FeatureModelToNodeTraceModel traceModel;
	/**
	 * The oracle used to reason over the circumstance to explain. Uses the CNF as input. Created lazily when needed and reset when the CNF changes.
	 */
	private Object oracle;

	@Override
	public Object getSubject() {
		return subject;
	}

	@Override
	public void setSubject(Object subject) {
		this.subject = subject;
	}

	@Override
	public IFeatureModel getFeatureModel() {
		return fm;
	}

	@Override
	public void setFeatureModel(IFeatureModel fm) {
		this.fm = fm;
		nodeCreator = null;
		cnf = null;
		traceModel = null;
		oracle = null;
	}

	/**
	 * Returns the node creator. Creates it first if necessary.
	 *
	 * @return the node creator
	 */
	protected AdvancedNodeCreator getNodeCreator() {
		if ((nodeCreator == null) && (getFeatureModel() != null)) {
			nodeCreator = createNodeCreator();
		}
		return nodeCreator;
	}

	/**
	 * Creates a new node creator.
	 *
	 * @return a new node creator; not null
	 */
	protected AdvancedNodeCreator createNodeCreator() {
		final AdvancedNodeCreator nc = new AdvancedNodeCreator(getFeatureModel());
		nc.setIncludeBooleanValues(false);
		nc.setCnfType(CNFType.Regular);
		nc.setRecordTraceModel(true);
		return nc;
	}

	/**
	 * Returns a formula representation of the feature model in CNF (conjunctive normal form). Creates it first if necessary.
	 *
	 * @return a formula representation of the feature model in CNF
	 */
	protected Node getCnf() throws IllegalStateException {
		if ((cnf == null) && (getFeatureModel() != null)) {
			cnf = createCnf();
		}
		return cnf;
	}

	/**
	 * Creates the formula representation of the feature model in CNF (conjunctive normal form).
	 *
	 * @return the CNF; not null
	 */
	protected Node createCnf() {
		return getNodeCreator().createNodes();
	}

	/**
	 * Returns the trace model.
	 *
	 * @return the trace model
	 */
	public FeatureModelToNodeTraceModel getTraceModel() {
		if ((traceModel == null) && (getFeatureModel() != null)) {
			traceModel = createTraceModel();
		}
		return traceModel;
	}

	/**
	 * Creates the trace model.
	 *
	 * @return the trace model; not null
	 */
	protected FeatureModelToNodeTraceModel createTraceModel() {
		return getNodeCreator().getTraceModel();
	}

	/**
	 * Returns the oracle. Creates it first if necessary.
	 *
	 * @return the oracle; not null
	 */
	protected Object getOracle() {
		if ((oracle == null) && (getFeatureModel() != null)) {
			oracle = createOracle();
		}
		return oracle;
	}

	/**
	 * Sets the oracle to null.
	 */
	protected void resetOracle() {
		oracle = null;
	}

	/**
	 * Returns a new oracle.
	 *
	 * @return a new oracle; not null
	 */
	protected abstract Object createOracle();

	/**
	 * Returns an explanation for the given clauses.
	 *
	 * @param clauseIndexes indexes of clauses that serve as an explanation
	 * @return an explanation
	 */
	protected Explanation getExplanation(Set<Integer> clauseIndexes) {
		final Explanation explanation = getConcreteExplanation();
		for (final Integer clauseIndex : clauseIndexes) {
			final Reason reason = getReason(clauseIndex);
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
	protected Explanation getExplanation(Collection<Set<Integer>> clauseIndexes) {
		final List<Explanation> explanations = new LinkedList<>();
		for (final Set<Integer> c : clauseIndexes) {
			explanations.add(getExplanation(c));
		}
		final Explanation cumulatedExplanation = getConcreteExplanation();
		cumulatedExplanation.setExplanationCount(0);
		Explanation shortestExplanation = null;
		for (final Explanation explanation : explanations) {
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
	protected Reason getReason(int clauseIndex) {
		return new FeatureModelReason(getTraceModel().getTrace(clauseIndex));
	}

	/**
	 * Returns a new concrete explanation.
	 *
	 * @return a new concrete explanation; not null
	 */
	protected abstract Explanation getConcreteExplanation();
}
