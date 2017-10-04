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
package de.ovgu.featureide.fm.core.base;

import org.junit.Assert;
import org.junit.Test;

import de.ovgu.featureide.Commons;

/**
 * Test case to verify that the analyzer recognizes false optional feature in 'and', 'or' and 'alternative' groups.
 *
 * @author Joshua Sprey
 */
public class FalseOptionalAndOrAlternativeAnalyserTest {

	@Test
	public void checkFalseOptionals() {
		final IFeatureModel model = Commons.loadTestFeatureModelFromFile("false_optional_test.xml");
		model.getAnalyser().analyzeFeatureModel(null);
		Assert.assertEquals(model.getAnalyser().getCachedFalseOptionalFeatures().size(), 3);
	}
}
