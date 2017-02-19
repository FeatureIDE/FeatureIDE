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

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Generates explanations for false-optional features using {@link LTMS}.
 * 
 * @author Sofia Ananieva
 * @author Timo Guenther
 */
public class FalseOptionalFeatureExplanationCreator extends ExplanationCreator {
	/** the false-optional feature in the feature model */
	private IFeature falseOptionalFeature;
	
	/**
	 * Constructs a new instance of this class.
	 */
	public FalseOptionalFeatureExplanationCreator() {
		this(null);
	}
	
	/**
	 * Constructs a new instance of this class.
	 * @param fm the feature model context
	 */
	public FalseOptionalFeatureExplanationCreator(IFeatureModel fm) {
		this(fm, null);
	}
	
	/**
	 * Constructs a new instance of this class.
	 * @param fm the feature model context
	 * @param falseOptionalFeature the false-optional feature in the feature model
	 */
	public FalseOptionalFeatureExplanationCreator(IFeatureModel fm, IFeature falseOptionalFeature) {
		super(fm);
		setFalseOptionalFeature(falseOptionalFeature);
	}
	
	/**
	 * Returns the false-optional feature in the feature model.
	 * @return the false-optional feature in the feature model
	 */
	public IFeature getFalseOptionalFeature() {
		return falseOptionalFeature;
	}
	
	/**
	 * Sets the false-optional feature in the feature model.
	 * @param falseOptionalFeature the false-optional feature in the feature model
	 */
	public void setFalseOptionalFeature(IFeature falseOptionalFeature) {
		this.falseOptionalFeature = falseOptionalFeature;
	}
	
	/**
	 * Returns an explanation why the specified feature of the specified feature model is false-optional.
	 * Sets initial truth value assumptions of the false-optional feature to false and its parent to true.
	 * Then propagates the values until a violation in a clause occurs.
	 * @return an explanation why the specified feature of the specified feature model is false-optional
	 */
	@Override
	public Explanation getExplanation() {
		final LTMS ltms = getLTMS();
		ltms.clearPremises();
		ltms.addPremise(getFalseOptionalFeature().getName(), false);
		ltms.addPremise(FeatureUtils.getParent(getFalseOptionalFeature()).getName(), true);
		final Explanation explanation = ltms.getExplanation();
		if (explanation == null) {
			return null;
		}
		explanation.setDefectFalseOptionalFeature(getFalseOptionalFeature());
		return explanation;
	}
}