/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.explanations;

import java.util.LinkedList;
import java.util.List;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * Generates explanations for defects in feature models.
 * Each type of defect is handled in its own concrete subclass.
 * 
 * @author Timo Guenther
 * @author Sofia Ananieva
 * @see DeadFeatureExplanationCreator
 * @see FalseOptionalFeatureExplanationCreator
 * @see RedundantConstraintExplanationCreator
 */
public abstract class ExplanationCreator {
	/** The feature model context. */
	private IFeatureModel fm;
	/**
	 * A formula representation of the feature model in CNF (conjunctive normal form).
	 * The CNF is created lazily when needed and reset when the feature model changes.
	 * This makes it possible to reuse the CNF for different defects of the same type in the same feature model.
	 */
	private Node cnf;
	/**
	 * The LTMS with the CNF as input.
	 * The LTMS is created lazily when needed and reset when the CNF changes.
	 */
	private LTMS ltms;
	
	/**
	 * Constructs a new instance of this class.
	 */
	public ExplanationCreator() {
		this(null);
	}
	
	/**
	 * Constructs a new instance of this class.
	 * @param fm the feature model context
	 */
	public ExplanationCreator(IFeatureModel fm) {
		setFeatureModel(fm);
	}
	
	/**
	 * Returns the feature model context.
	 * @return the feature model context
	 */
	public IFeatureModel getFeatureModel() {
		return fm;
	}
	
	/**
	 * Sets the feature model context.
	 * @param fm the feature model context
	 */
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
	 * Also removes all clauses containing closed literals (true and false) 
	 * @param cnf formula representation of the feature model in CNF
	 * @throws IllegalArgumentException if the given formula is not in CNF
	 */
	protected void setCNF(Node cnf) throws IllegalArgumentException {
		if (cnf != null && (!(cnf instanceof And) || !cnf.isConjunctiveNormalForm())) {
			throw new IllegalArgumentException("Formula is not in CNF");
		}
		this.cnf = cnf;
		setLTMS(null);
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
	
	/**
	 * Returns the LTMS.
	 * Creates it first if necessary.
	 * @return the LTMS; not null
	 */
	protected LTMS getLTMS() {
		if (ltms == null) {
			setLTMS(createLTMS());
		}
		return ltms;
	}
	
	/**
	 * Sets the LTMS.
	 * @param ltms the LTMS
	 */
	protected void setLTMS(LTMS ltms) {
		this.ltms = ltms;
	}
	
	/**
	 * Returns a new LTMS with the CNF.
	 * @return a new LTMS with the CNF; not null
	 */
	protected LTMS createLTMS() {
		return new LTMS(getCNF());
	}
	
	/**
	 * Returns an explanation for the specified defect in the feature model or null if none could be generated.
	 * The information which defect this is might be provided using setters of the concrete subclasses.
	 * @return an explanation for the specified defect in the feature model or null if none could be generated
	 * @throws IllegalStateException if no defect is specified
	 */
	public abstract Explanation getExplanation() throws IllegalStateException;
}