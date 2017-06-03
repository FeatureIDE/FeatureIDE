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

import org.prop4j.Literal;
import org.prop4j.explain.solvers.MusExtractor;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.FalseOptionalFeatureExplanationCreator;

/**
 * Implementation of {@link FalseOptionalFeatureExplanationCreator} using a {@link MusExtractor MUS extractor}.
 * 
 * @author Timo G&uuml;nther
 */
public class MusFalseOptionalFeatureExplanationCreator extends MusFeatureModelExplanationCreator implements FalseOptionalFeatureExplanationCreator {
	/** The false-optional feature in the feature model. */
	private IFeature falseOptionalFeature;
	
	/**
	 * Constructs a new instance of this class.
	 */
	protected MusFalseOptionalFeatureExplanationCreator() {
		this(null);
	}
	
	/**
	 * Constructs a new instance of this class.
	 * @param fm the feature model context
	 */
	protected MusFalseOptionalFeatureExplanationCreator(IFeatureModel fm) {
		this(fm, null);
	}
	
	/**
	 * Constructs a new instance of this class.
	 * @param fm the feature model context
	 * @param falseOptionalFeature the false-optional feature in the feature model
	 */
	protected MusFalseOptionalFeatureExplanationCreator(IFeatureModel fm, IFeature falseOptionalFeature) {
		super(fm);
		setFalseOptionalFeature(falseOptionalFeature);
	}
	
	@Override
	public IFeature getFalseOptionalFeature() {
		return falseOptionalFeature;
	}
	
	@Override
	public void setFalseOptionalFeature(IFeature falseOptionalFeature) {
		this.falseOptionalFeature = falseOptionalFeature;
	}
	
	@Override
	public Explanation getExplanation() throws IllegalStateException {
		final MusExtractor oracle = getOracle();
		final Explanation explanation;
		oracle.push();
		try {
			oracle.addFormula(new Literal(getFalseOptionalFeature().getName(), false));
			oracle.addFormula(new Literal(FeatureUtils.getParent(getFalseOptionalFeature()).getName(), true));
			explanation = getExplanation(oracle.getMinimalUnsatisfiableSubset());
		} finally {
			oracle.pop();
		}
		explanation.setDefectFalseOptionalFeature(getFalseOptionalFeature());
		return explanation;
	}
}
