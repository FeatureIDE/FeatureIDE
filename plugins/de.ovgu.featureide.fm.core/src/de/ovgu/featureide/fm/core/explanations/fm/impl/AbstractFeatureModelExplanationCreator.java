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
	 * Constructs a new instance of this class.
	 */
	public AbstractFeatureModelExplanationCreator() {
		this(null);
	}

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param fm the feature model contexts
	 */
	public AbstractFeatureModelExplanationCreator(IFeatureModel fm) {
		setFeatureModel(fm);
	}

	@Override
	public IFeatureModel getFeatureModel() {
		return fm;
	}

	@Override
	public void setFeatureModel(IFeatureModel fm) {
		this.fm = fm;
		setNodeCreator();
		setCnf();
	}

	/**
	 * Returns the node creator. Creates it first if necessary.
	 *
	 * @return the node creator
	 */
	protected AdvancedNodeCreator getNodeCreator() {
		return nodeCreator;
	}

	/**
	 * Sets the node creator.
	 */
	protected void setNodeCreator() {
		if (getFeatureModel() == null) {
			nodeCreator = null;
			return;
		}
		nodeCreator = createNodeCreator();
	}

	/**
	 * Creates a new node creator.
	 *
	 * @return a new node creator
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
	 * @return a formula representation of the feature model in CNF; not null
	 * @throws IllegalStateException if the CNF could not be created
	 */
	protected Node getCnf() throws IllegalStateException {
		if (cnf == null) {
			try {
				setCnf();
			} catch (final IllegalArgumentException e) {
				throw new IllegalStateException(e);
			}
		}
		return cnf;
	}

	/**
	 * Sets the formula representation of the feature model in CNF (conjunctive normal form).
	 *
	 * @return the CNF
	 */
	protected Node setCnf() {
		final IFeatureModel fm = getFeatureModel();
		if (fm == null) {
			cnf = null;
			traceModel = null;
			return cnf;
		}
		final AdvancedNodeCreator nc = getNodeCreator();
		cnf = nc.createNodes();
		traceModel = nc.getTraceModel();
		return cnf;
	}

	/**
	 * Returns the trace model.
	 *
	 * @return the trace model
	 */
	public FeatureModelToNodeTraceModel getTraceModel() {
		return traceModel;
	}

	/**
	 * Returns an explanation for the given clauses.
	 *
	 * @param clauseIndexes indexes of clauses that serve as an explanation
	 * @return an explanation
	 */
	protected Explanation getExplanation(Set<Integer> clauseIndexes) {
		final Explanation explanation = getConcreteExplanation();
		for (final Integer clauseIndex : clauseIndexes) {
			explanation.addReason(getReason(clauseIndex));
		}
		return explanation;
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
	 * @return a new concrete explanation
	 */
	protected abstract Explanation getConcreteExplanation();
}
