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

import java.util.Map;

import org.prop4j.Node;
import org.prop4j.explain.solvers.MusExtractor;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.ModelType;
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
	}
	
	/**
	 * {@inheritDoc}
	 * 
	 * <p>
	 * Does not contain any of the constraints.
	 * The constraints are only added later during explaining.
	 * This is faster than creating the complete CNF and repeatedly removing the redundant constraints from it.
	 * </p>
	 */
	@Override
	protected Node createCnf() throws IllegalStateException {
		final AdvancedNodeCreator nc = new AdvancedNodeCreator(getFeatureModel());
		nc.setCnfType(CNFType.Regular);
		nc.setModelType(ModelType.OnlyStructure);
		nc.setIncludeBooleanValues(false);
		return nc.createNodes();
	}
	
	@Override
	public Explanation getExplanation() throws IllegalStateException {
		final Explanation cumulatedExplanation = new Explanation();
		cumulatedExplanation.setExplanationCount(0);
		final MusExtractor oracle = getOracle();
		oracle.push();
		try {
			//Add each constraint but the redundant one.
			for (final IConstraint constraint : getFeatureModel().getConstraints()) {
				if (constraint != redundantConstraint) {
					oracle.addFormula(constraint.getNode());
				}
			}
			
			//Explain each contradicting assignment of the redundant constraint.
			for (final Map<Object, Boolean> assignment : getRedundantConstraint().getNode().getContradictingAssignments()) {
				oracle.push();
				try {
					oracle.addAssumptions(assignment);
					final Explanation explanation = getExplanation(oracle.getMinimalUnsatisfiableSubset());
					cumulatedExplanation.addExplanation(explanation);
				} finally {
					oracle.pop();
				}
			}
		} finally {
			oracle.pop();
		}
		cumulatedExplanation.setDefectRedundantConstraint(getRedundantConstraint());
		return cumulatedExplanation;
	}
}