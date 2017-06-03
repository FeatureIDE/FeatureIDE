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
package de.ovgu.featureide.fm.core.explanations.impl.mus;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Literal.FeatureAttribute;
import org.prop4j.Node;
import org.prop4j.explain.solvers.MusExtractor;
import org.prop4j.explain.solvers.SatSolverFactory;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.RedundantConstraintExplanationCreator;

/**
 * Implementation of {@link RedundantConstraintExplanationCreator} using a {@link MusExtractor MUS extractor}.
 * 
 * @author Timo G&uuml;nther
 */
public class MusRedundantConstraintExplanationCreator extends MusFeatureModelExplanationCreator implements RedundantConstraintExplanationCreator {
	/** The redundant constraint in the feature model. */
	private IConstraint redundantConstraint;
	/**
	 * The CNF without the clauses of the redundant constraint.
	 * It is later used as the input for the LTMS.
	 * It is stored separately from the CNF so the CNF does not have to be overridden and can continue to be reused.
	 * It is created lazily when needed and reset when any of the variables it depends on is changed:
	 * the feature model, the feature model's CNF representation or the redundant constraint.
	 */
	private Node cnfWithoutRedundantConstraintClauses;
	
	/**
	 * Constructs a new instance of this class.
	 */
	protected MusRedundantConstraintExplanationCreator() {
		this(null);
	}
	
	/**
	 * Constructs a new instance of this class.
	 * @param fm the feature model context
	 */
	protected MusRedundantConstraintExplanationCreator(IFeatureModel fm) {
		this(fm, null);
	}
	
	/**
	 * Constructs a new instance of this class.
	 * @param fm the feature model context
	 * @param redundantConstraint the redundant constraint in the feature model
	 */
	protected MusRedundantConstraintExplanationCreator(IFeatureModel fm, IConstraint redundantConstraint) {
		super(fm);
		setRedundantConstraint(redundantConstraint);
	}
	
	@Override
	public IConstraint getRedundantConstraint() {
		return redundantConstraint;
	}
	
	@Override
	public void setRedundantConstraint(IConstraint redundantConstraint) {
		this.redundantConstraint = redundantConstraint;
		setCNFWithoutRedundantConstraintClauses(null);
	}
	
	/**
	 * Returns the CNF without the clauses of the redundant constraint.
	 * Creates it first if necessary.
	 * @return the CNF without the clauses of the redundant constraint; not null
	 */
	protected Node getCNFWithoutRedundantConstraintClauses() {
		if (cnfWithoutRedundantConstraintClauses == null) {
			setCNFWithoutRedundantConstraintClauses(createCNFWithoutRedundantConstraintClauses());
		}
		return cnfWithoutRedundantConstraintClauses;
	}
	
	/**
	 * Sets the CNF without the clauses of the redundant constraint.
	 * @param cnfWithoutRedundantConstraintClauses the CNF without the clauses of the redundant constraint
	 */
	protected void setCNFWithoutRedundantConstraintClauses(Node cnfWithoutRedundantConstraintClauses) {
		this.cnfWithoutRedundantConstraintClauses = cnfWithoutRedundantConstraintClauses;
		setOracle(null);
	}
	
	/**
	 * Creates a copy of the CNF without the clauses of the redundant constraint.
	 * @return a copy of the CNF without the clauses of the redundant constraint; not null
	 */
	protected Node createCNFWithoutRedundantConstraintClauses() {
		return removeRedundantConstraintClauses(getCnf());
	}
	
	/**
	 * Returns a copy of the given CNF without clauses of the redundant constraint.
	 * @param cnf CNF to check
	 * @return a copy of the given CNF without clauses of the redundant constraint
	 * @throws IllegalStateException if the redundant constraint is not set
	 */
	private Node removeRedundantConstraintClauses(Node cnf) throws IllegalStateException {
		if (getRedundantConstraint() == null) {
			throw new IllegalStateException("Missing redundant constraint");
		}
		final List<Node> clauses = new LinkedList<>();
		clause: for (final Node clause : cnf.getChildren()) {
			for (final Literal literal : clause.getLiterals()) {
				if (literal.getSourceAttribute() == FeatureAttribute.CONSTRAINT
						&& getFeatureModel().getConstraints().get(literal.getSourceIndex()) == redundantConstraint) {
					continue clause;
				}
			}
			clauses.add(clause);
		}
		return new And(clauses.toArray());
	}
	
	@Override
	protected MusExtractor createOracle() {
		final MusExtractor oracle = SatSolverFactory.getDefault().getMusExtractor();
		oracle.addFormula(getCNFWithoutRedundantConstraintClauses());
		return oracle;
	}
	
	@Override
	public Explanation getExplanation() throws IllegalStateException {
		final Explanation cumulatedExplanation = new Explanation();
		cumulatedExplanation.setExplanationCount(0);
		final MusExtractor oracle = getOracle();
		for (final Map<Object, Boolean> assignment : getRedundantConstraint().getNode().getContradictingAssignments()) {
			oracle.push();
			try {
				for (final Entry<Object, Boolean> e : assignment.entrySet()) {
					oracle.addFormula(new Literal(e.getKey(), e.getValue()));
				}
				final Explanation explanation = getExplanation(oracle.getMinimalUnsatisfiableSubset());
				cumulatedExplanation.addExplanation(explanation);
			} finally {
				oracle.pop();
			}
		}
		cumulatedExplanation.setDefectRedundantConstraint(getRedundantConstraint());
		return cumulatedExplanation;
	}
}