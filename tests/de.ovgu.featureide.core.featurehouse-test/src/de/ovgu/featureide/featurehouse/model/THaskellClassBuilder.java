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
package de.ovgu.featureide.featurehouse.model;

import static org.junit.Assert.assertEquals;

import java.util.LinkedList;

import org.junit.Test;

/**
 * Test for {@link FeatureHouseModelBuilder} of Haskel files.
 *
 * @see HaskellClassBuilder
 * @author Jens Meinicke
 */
public class THaskellClassBuilder {

	private final HaskellClassBuilder builder = new HaskellClassBuilder(null);

	// METHOD TEST 1
	private final String TEST_METHOD_1 = "mapResult :: (a -> Result b err) -> Result a err -> Result b err";
	private final String EXPECTED_NAME_METHOD_1 = "mapResult";
	private final String EXPECTED_PARAMETER_1_METHOD_1 = "(a -> Result b err) -> Result a err -> Result b err";

	@Test
	public void methodTest1() {
		final LinkedList<String> method = builder.getMethod(TEST_METHOD_1);
		assertEquals(EXPECTED_NAME_METHOD_1, method.get(0));
		assertEquals(EXPECTED_PARAMETER_1_METHOD_1, method.get(1));
	}
}
