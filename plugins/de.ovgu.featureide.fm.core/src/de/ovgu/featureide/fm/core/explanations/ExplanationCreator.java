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
package de.ovgu.featureide.fm.core.explanations;

import java.util.LinkedList;
import java.util.List;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * Generates explanations for defects in feature models.
 * Each type of defect is handled in its own concrete subclass.
 * 
 * @author Timo Guenther
 * @author Sofia Ananieva
 * 
 * @see DeadFeatureExplanationCreator
 * @see FalseOptionalFeatureExplanationCreator
 * @see RedundantConstraintExplanationCreator
 */
public abstract class ExplanationCreator<T extends IFeatureModelElement> {

	/** The feature model element that should be explained. */
	private T defectElement;

	/**
	 * Returns the defect element in the feature model.
	 * 
	 * @return the defect element in the feature model
	 */
	public T getDefectElement() {
		return defectElement;
	}

	/**
	 * Sets the defect element in the feature model.
	 * 
	 * @param deadFeature the defect element in the feature model
	 */
	public void setDefectElement(T defectElement) {
		this.defectElement = defectElement;
	}

	/**
	 * Returns a copy of the given node in CNF.
	 * 
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
	 * 
	 * @param cnf formula in CNF; not null
	 * @return a copy of the given CNF without tautologies; not null
	 */
	private static Node removeTautologies(Node cnf) {
		final List<Node> cnfClauses = new LinkedList<>();
		cnfClause: for (final Node cnfClause : cnf.getChildren()) {
			for (final Literal literal : cnfClause.getLiterals()) {
				if (literal.var == NodeCreator.varTrue && literal.positive || literal.var == NodeCreator.varFalse && !literal.positive) {
					continue cnfClause;
				}
			}
			cnfClauses.add(cnfClause);
		}
		return new And(cnfClauses.toArray());
	}

	/**
	 * Returns an explanation for the specified defect in the feature model or null if none could be generated.
	 * The information which defect this is might be provided using setters of the concrete subclasses.
	 * <br/><br/>
	 * The LTMS is created lazily when needed in the respective subclasses by the given formula and reset when the CNF changes.
	 * 
	 * @param formula The {@link FeatureModelFormula formula} for a feature model
	 * @return an explanation for the specified defect in the feature model or null if none could be generated
	 * @throws IllegalStateException if no defect is specified
	 */
	public abstract Explanation getExplanation(FeatureModelFormula formula) throws IllegalStateException;

}