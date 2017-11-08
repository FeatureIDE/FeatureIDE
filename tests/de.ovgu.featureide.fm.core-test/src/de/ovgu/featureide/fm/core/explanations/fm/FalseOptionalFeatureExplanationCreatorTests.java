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
package de.ovgu.featureide.fm.core.explanations.fm;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import de.ovgu.featureide.Commons;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Tests for {@link FalseOptionalFeatureExplanationCreator}.
 *
 * @author Timo G&uuml;nther
 */
public class FalseOptionalFeatureExplanationCreatorTests
		extends FeatureModelExplanationCreatorTests<IFeature, FalseOptionalFeatureExplanation, FalseOptionalFeatureExplanationCreator> {

	@Test
	public void testCar() {
		final FalseOptionalFeatureExplanationCreator c = getInstance();
		final IFeatureModel fm = Commons.loadTestFeatureModelFromFile("car.xml");
		c.setFeatureModel(fm);
		c.setSubject(fm.getFeature("Automatic"));
		assertTrue(isValid(c.getExplanation()));
		c.setSubject(fm.getFeature("Navigation"));
		assertTrue(isValid(c.getExplanation()));
		c.setSubject(fm.getFeature("Ports"));
		assertTrue(isValid(c.getExplanation()));
		c.setSubject(fm.getFeature("USB"));
		assertTrue(isValid(c.getExplanation()));
	}

	@Override
	protected FalseOptionalFeatureExplanationCreator getInstance() {
		return FeatureModelExplanationCreatorFactory.getDefault().getFalseOptionalFeatureExplanationCreator();
	}
}
