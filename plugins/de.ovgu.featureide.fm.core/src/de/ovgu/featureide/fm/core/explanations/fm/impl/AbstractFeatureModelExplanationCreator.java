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

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;
import de.ovgu.featureide.fm.core.editing.FeatureModelToNodeTraceModel;
import de.ovgu.featureide.fm.core.explanations.Reason;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanation;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelReason;
import de.ovgu.featureide.fm.core.explanations.impl.AbstractExplanationCreator;

/**
 * Abstract implementation of {@link FeatureModelExplanationCreator}.
 *
 * @param <S> subject
 * @param <E> explanation
 * @param <O> oracle
 * @author Timo G&uuml;nther
 */
public abstract class AbstractFeatureModelExplanationCreator<S, E extends FeatureModelExplanation<S>, O> extends AbstractExplanationCreator<S, E, O>
		implements FeatureModelExplanationCreator<S, E> {

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
		setOracle(null);
	}

	/**
	 * Returns the node creator. Creates it first if necessary.
	 *
	 * @return the node creator; not null
	 * @throws IllegalStateException if the feature model is not set
	 */
	protected AdvancedNodeCreator getNodeCreator() throws IllegalStateException {
		if (nodeCreator == null) {
			nodeCreator = createNodeCreator();
		}
		return nodeCreator;
	}

	/**
	 * Creates a new node creator.
	 *
	 * @return a new node creator; not null
	 * @throws IllegalStateException if the feature model is not set
	 */
	protected AdvancedNodeCreator createNodeCreator() throws IllegalStateException {
		final IFeatureModel fm = getFeatureModel();
		if (fm == null) {
			throw new IllegalStateException("Feature model not set");
		}
		final AdvancedNodeCreator nc = new AdvancedNodeCreator(fm);
		nc.setIncludeBooleanValues(false);
		nc.setCnfType(CNFType.Regular);
		nc.setRecordTraceModel(true);
		return nc;
	}

	/**
	 * Returns a formula representation of the feature model in CNF (conjunctive normal form). Creates it first if necessary.
	 *
	 * @return a formula representation of the feature model in CNF; not null
	 * @throws IllegalStateException if the formula is not set
	 */
	protected Node getCnf() throws IllegalStateException {
		if (cnf == null) {
			cnf = createCnf();
		}
		return cnf;
	}

	/**
	 * Creates the formula representation of the feature model in CNF (conjunctive normal form).
	 *
	 * @return the CNF; not null
	 * @throws IllegalStateException if the formula is not set
	 */
	protected Node createCnf() throws IllegalStateException {
		return getNodeCreator().createNodes();
	}

	/**
	 * Returns the trace model.
	 *
	 * @return the trace model; not null
	 * @throws IllegalStateException if the feature model is not set
	 */
	public FeatureModelToNodeTraceModel getTraceModel() throws IllegalStateException {
		if (traceModel == null) {
			traceModel = createTraceModel();
		}
		return traceModel;
	}

	/**
	 * Creates the trace model.
	 *
	 * @return the trace model; not null
	 * @throws IllegalStateException if the feature model is not set
	 */
	protected FeatureModelToNodeTraceModel createTraceModel() throws IllegalStateException {
		return getNodeCreator().getTraceModel();
	}

	@Override
	protected Reason<?> getReason(int clauseIndex) {
		return new FeatureModelReason(getTraceModel().getTrace(clauseIndex));
	}
}
