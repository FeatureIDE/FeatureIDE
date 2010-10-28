/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.configuration;

import junit.framework.JUnit4TestAdapter;
import junit.framework.TestCase;

import org.junit.Assert;
import org.junit.Test;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.configuration.SelectionNotPossibleException;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;


/**
 * Tests belonging to feature selections called configurations.
 * 
 * @author Thomas Thuem
 */
public class TConfiguration {
	
	@Test
	public void test1(){
		Assert.assertTrue(true);
	}
	
//	public static junit.framework.Test suite() {
//		return new JUnit4TestAdapter(TConfiguration.class);
//	}
//	
//	String fm = "S : [A] [B] C :: _S; %% not B;";
//
//	@Test
//	public void testValid1() throws TimeoutException, UnsupportedModelException {
//		Configuration c = createConfiguration(fm, false);
//		c.setManual("S", Selection.SELECTED);
//		c.setManual("C", Selection.SELECTED);
//		assertTrue(c.valid());
//	}
//
//	@Test
//	public void testValid2() throws TimeoutException, UnsupportedModelException {
//		Configuration c = createConfiguration(fm, true);
//		assertTrue(c.valid());
//	}
//
//	@Test
//	public void testValid3() throws TimeoutException, UnsupportedModelException {
//		Configuration c = createConfiguration(fm, false);
//		c.setManual("S", Selection.SELECTED);
//		c.setManual("A", Selection.SELECTED);
//		c.setManual("C", Selection.SELECTED);
//		assertTrue(c.valid());
//	}
//
//	@Test
//	public void testValid4() throws TimeoutException, UnsupportedModelException {
//		Configuration c = createConfiguration(fm, true);
//		c.setManual("A", Selection.SELECTED);
//		assertTrue(c.valid());
//	}
//
////	@Test
////	public void testValid5() throws TimeoutException, UnsupportedModelException {
////		Configuration c = createConfiguration(fm, false);
////		c.setManual("C", Selection.SELECTED);
////		assertTrue(c.validManually());
////	}
////
////	@Test
////	public void testValid6() throws TimeoutException, UnsupportedModelException {
////		Configuration c = createConfiguration(fm, true);
////		assertTrue(!c.validManually());
////	}
////
////	@Test
////	public void testValid7() throws TimeoutException, UnsupportedModelException {
////		Configuration c = createConfiguration(fm, false);
////		c.setManual("A", Selection.SELECTED);
////		c.setManual("C", Selection.SELECTED);
////		assertTrue(c.validManually());
////	}
////
////	@Test
////	public void testValid8() throws TimeoutException, UnsupportedModelException {
////		Configuration c = createConfiguration(fm, true);
////		c.setManual("A", Selection.SELECTED);
////		assertTrue(!c.validManually());
////	}
//
//	@Test
//	public void testValid9() throws TimeoutException, UnsupportedModelException {
//		Configuration c = createConfiguration(fm, true);
//		try {
//			c.setManual("B", Selection.SELECTED);
//		} catch (SelectionNotPossibleException e) {
//			assertTrue(true);
//		}
//	}
//
//	private Configuration createConfiguration(String fm, boolean propagate) throws UnsupportedModelException {
//		return new Configuration(readModel(fm), propagate);
//	}
//
//	private FeatureModel readModel(String grammar) throws UnsupportedModelException {
//		FeatureModel fm = new FeatureModel();
//		XmlFeatureModelReader reader = new XmlFeatureModelReader(fm);
//		reader.readFromString(grammar);
//		return fm;
//	}

}
