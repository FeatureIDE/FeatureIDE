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
package de.ovgu.featureide.fm.core.explanations.fm.impl.ltms;

import java.util.Collection;
import java.util.Set;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.explanations.fm.DeadFeatureExplanation;
import de.ovgu.featureide.fm.core.explanations.fm.DeadFeatureExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.impl.ltms.Ltms;

/**
 * Implementation of {@link DeadFeatureExplanationCreator} using an {@link Ltms LTMS}.
 *
 * @author Sofia Ananieva
 * @author Timo G&uuml;nther
 */
public class LtmsDeadFeatureExplanationCreator extends LtmsFeatureModelExplanationCreator implements DeadFeatureExplanationCreator {

	/** The dead feature in the feature model. */
	private IFeature deadFeature;

	/**
	 * Constructs a new instance of this class.
	 */
	public LtmsDeadFeatureExplanationCreator() {
		this(null);
	}

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param fm the feature model context
	 */
	public LtmsDeadFeatureExplanationCreator(IFeatureModel fm) {
		this(fm, null);
	}

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param fm the feature model context
	 * @param deadFeature the dead feature in the feature model
	 */
	public LtmsDeadFeatureExplanationCreator(IFeatureModel fm, IFeature deadFeature) {
		super(fm);
		setDeadFeature(deadFeature);
	}

	@Override
	public IFeature getDeadFeature() {
		return deadFeature;
	}

	@Override
	public void setDeadFeature(IFeature deadFeature) {
		this.deadFeature = deadFeature;
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p> Sets initial truth value assumptions of the dead feature to true. Then propagates the values until a violation in a clause occurs. </p>
	 */
	@Override
	public DeadFeatureExplanation getExplanation() throws IllegalStateException {
		final Ltms ltms = getLtms();
		ltms.clearPremises();
		ltms.addPremise(getDeadFeature().getName(), true);
		return getExplanation(ltms.getExplanations());
	}

	@Override
	protected DeadFeatureExplanation getExplanation(Collection<Set<Integer>> clauseIndexes) {
		return (DeadFeatureExplanation) super.getExplanation(clauseIndexes);
	}

	@Override
	protected DeadFeatureExplanation getConcreteExplanation() {
		return new DeadFeatureExplanation(getDeadFeature());
	}
}
