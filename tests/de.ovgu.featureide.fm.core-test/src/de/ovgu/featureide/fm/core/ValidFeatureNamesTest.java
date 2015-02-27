/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core;

import org.junit.Assert;
import org.junit.Test;

import de.ovgu.featureide.core.featuremodeling.FeatureModelingFMExtension;

/**
 * @author Marcus Pinnecke
 */
public class ValidFeatureNamesTest {
	
	/*//////////////////////////////////////////////////////////////////////////////////////////////
	 * 	Non Feature Modelling Composer
	 *//////////////////////////////////////////////////////////////////////////////////////////////

	@Test
	public void testNonFeatureModelling1() {
		validateForOthers("abc", true);
	}
	
	@Test
	public void testNonFeatureModelling2() {
		validateForOthers("aABC", true);
	}
	
	@Test
	public void testNonFeatureModelling3() {
		validateForOthers("aA10", true);
	}
	
	@Test
	public void testNonFeatureModelling4() {
		validateForOthers("(A10", false);
	}
	
	@Test
	public void testNonFeatureModelling5() {
		validateForOthers("A(10", false);
	}
	
	@Test
	public void testNonFeatureModelling6() {
		validateForOthers("\nabc", false);
	}
	
	@Test
	public void testNonFeatureModelling7() {
		validateForOthers("abc ", false);
	}
	
	@Test
	public void testNonFeatureModelling8() {
		validateForOthers("9abc ", false);
	}
	
	@Test
	public void testNonFeatureModelling9() {
		validateForOthers("under_score", true);
	}
	
	@Test
	public void testNonFeatureModelling10() {
		validateForOthers("a[]", false);
	}
	
	/*//////////////////////////////////////////////////////////////////////////////////////////////
	 * 	Feature Modelling
	 *//////////////////////////////////////////////////////////////////////////////////////////////
	
	@Test
	public void testFeatureModelling1() {
		validateForFeatureModelling("abc", true);
	}
	
	@Test
	public void testFeatureModelling2() {
		validateForFeatureModelling("aABC", true);
	}
	
	@Test
	public void testFeatureModelling3() {
		validateForFeatureModelling("aA10", true);
	}
	
	@Test
	public void testFeatureModelling4() {
		validateForFeatureModelling("(A10", false);
	}
	
	@Test
	public void testFeatureModelling5() {
		validateForFeatureModelling("A(10", false);
	}
	
	@Test
	public void testFeatureModelling6() {
		validateForFeatureModelling("\nabc", false);
	}
	
	@Test
	public void testFeatureModelling7() {
		validateForFeatureModelling("abc ", true);
	}
	
	@Test
	public void testFeatureModelling8() {
		validateForFeatureModelling(" ", false);
	}
	
	@Test
	public void testFeatureModelling9() {
		validateForFeatureModelling("a bc", true);
	}
	
	@Test
	public void testFeatureModelling10() {
		validateForFeatureModelling(" a bc ", true);
	}
	
	@Test
	public void testFeatureModelling11() {
		validateForFeatureModelling("9", true);
	}
	
	@Test
	public void testFeatureModelling12() {
		validateForFeatureModelling("[2] B", true);
	}
	
	@Test
	public void testFeatureModelling13() {
		validateForFeatureModelling("under_score", true);
	}
	
	@Test
	public void testFeatureModelling14() {
		validateForFeatureModelling("a[]", true);
	}
	
	/*//////////////////////////////////////////////////////////////////////////////////////////////
	 * 	Private methods
	 *//////////////////////////////////////////////////////////////////////////////////////////////
	
	private void validateForOthers(final String featureName, final boolean expected) {
		validateName(new FMComposerExtension(), featureName, expected);		
	}
	
	private void validateForFeatureModelling(final String featureName, final boolean expected) {
		validateName(new FeatureModelingFMExtension(), featureName, expected);		
	}
	
	private void validateName(final IFMComposerExtension comp, final String featureName, final boolean expected) {
		Assert.assertEquals(expected, comp.isValidFeatureName(featureName));
	}
}
