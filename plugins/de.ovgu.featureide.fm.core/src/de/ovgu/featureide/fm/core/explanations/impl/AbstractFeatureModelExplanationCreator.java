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

import java.util.LinkedList;
import java.util.List;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.explanations.FeatureModelExplanationCreator;

/**
 * Abstract implementation of {@link FeatureModelExlanationCreator}.
 * 
 * @author Timo Guenther
 */
public abstract class AbstractFeatureModelExplanationCreator implements FeatureModelExplanationCreator {
	/** The feature model context. */
	private IFeatureModel fm;
	/**
	 * A formula representation of the feature model in CNF (conjunctive normal form).
	 * The CNF is created lazily when needed and reset when the feature model changes.
	 * This makes it possible to reuse the CNF for different defects of the same type in the same feature model.
	 */
	private Node cnf;
	
	/**
	 * Constructs a new instance of this class.
	 */
	public AbstractFeatureModelExplanationCreator() {
		this(null);
	}
	
	/**
	 * Constructs a new instance of this class.
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
		setCNF(null);
	}
	
	/**
	 * Returns a formula representation of the feature model in CNF (conjunctive normal form).
	 * Creates it first if necessary.
	 * @return a formula representation of the feature model in CNF; not null
	 * @throws IllegalStateException if the CNF could not be created
	 */
	protected Node getCNF() throws IllegalStateException {
		if (cnf == null) {
			try {
				setCNF(createCNF());
			} catch (IllegalArgumentException e) {
				throw new IllegalStateException(e);
			}
		}
		return cnf;
	}
	
	/**
	 * Sets the formula representation of the feature model in CNF (conjunctive normal form).
	 * Also removes all clauses containing closed literals (true and false).
	 * @param cnf formula representation of the feature model in CNF
	 * @throws IllegalArgumentException if the given formula is not in CNF
	 */
	protected void setCNF(Node cnf) throws IllegalArgumentException {
		if (cnf != null && (!(cnf instanceof And) || !cnf.isConjunctiveNormalForm())) {
			throw new IllegalArgumentException("Formula is not in CNF");
		}
		this.cnf = cnf;
	}
	
	/**
	 * Creates the formula representation of the feature model in CNF (conjunctive normal form).
	 * @return the formula representation of the feature model in CNF; not null
	 * @throws IllegalStateException if the feature model is null
	 */
	protected Node createCNF() throws IllegalStateException {
		return createCNF(NodeCreator.createNodes(fm));
	}
	
	/**
	 * Returns a copy of the given node in CNF.
	 * @param node node to transform
	 * @return a copy of the given node in CNF; not null
	 */
	protected Node createCNF(Node node) {
		return removeTautologies(node.toCNF());
	}
	
	/**
	 * Returns a copy of the given CNF without tautologies.
	 * {@link NodeCreator} creates closed literals (true and false) during elimination of abstract variables.
	 * Clauses containing such literals can be removed as they do not change the semantics of the formula.
	 * @param cnf formula in CNF; not null
	 * @return a copy of the given CNF without tautologies; not null
	 */
	private static Node removeTautologies(Node cnf) {
		final List<Node> cnfClauses = new LinkedList<>();
		cnfClause: for (final Node cnfClause : cnf.getChildren()) {
			for (final Literal literal : cnfClause.getLiterals()) {
				if (literal.var == NodeCreator.varTrue && literal.positive
						|| literal.var == NodeCreator.varFalse && !literal.positive) {
					continue cnfClause;
				}
			}
			cnfClauses.add(cnfClause);
		}
		return new And(cnfClauses.toArray());
	}
}