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

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Generates explanations for dead features and void feature models using {@link LTMS}.
 * 
 * @author Sofia Ananieva
 * @author Timo Guenther
 */
public class DeadFeatureExplanationCreator extends ExplanationCreator {
	/** the dead feature in the feature model */
	private IFeature deadFeature;
	
	/**
	 * Constructs a new instance of this class.
	 */
	public DeadFeatureExplanationCreator() {
		this(null);
	}
	
	/**
	 * Constructs a new instance of this class.
	 * @param fm the feature model context
	 */
	public DeadFeatureExplanationCreator(IFeatureModel fm) {
		this(fm, null);
	}
	
	/**
	 * Constructs a new instance of this class.
	 * @param fm the feature model context
	 * @param deadFeature the dead feature in the feature model
	 */
	public DeadFeatureExplanationCreator(IFeatureModel fm, IFeature deadFeature) {
		super(fm);
		setDeadFeature(deadFeature);
	}
	
	/**
	 * Returns the dead feature in the feature model.
	 * @return the dead feature in the feature model
	 */
	public IFeature getDeadFeature() {
		return deadFeature;
	}
	
	/**
	 * Sets the dead feature in the feature model.
	 * @param deadFeature the dead feature in the feature model
	 */
	public void setDeadFeature(IFeature deadFeature) {
		this.deadFeature = deadFeature;
	}
	
	/**
	 * Returns an explanation why the specified feature of the specified feature model is dead.
	 * A dead root feature also means a void feature model.
	 * Sets initial truth value assumptions of the dead feature to true.
	 * Then propagates the values until a violation in a clause occurs.
	 * @return an explanation why the specified feature of the specified feature model is dead
	 */
	@Override
	public Explanation getExplanation() {
		final LTMS ltms = getLTMS();
		ltms.clearPremises();
		ltms.addPremise(getDeadFeature().getName(), true);
		final Explanation explanation = ltms.getExplanation();
		if (explanation == null) {
			return null;
		}
		explanation.setDefectDeadFeature(getDeadFeature());
		return explanation;
	}
}