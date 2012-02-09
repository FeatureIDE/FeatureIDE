/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.IFeatureModelReader;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.guidsl.GuidslReader;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;

/**
 * Tests belonging to feature selections called configurations.
 * 
 * @author Thomas Thuem
 * @author Fabian Benduhn
 */
public class TConfiguration {

	public static FeatureModel fm = loadGUIDSL("S : [A] [B] C :: _S; %% not B;");

	@Test
	public void testSelection1() {
		Configuration c = new Configuration(fm, false);
		c.setManual("C", Selection.SELECTED);
		assertTrue(c.valid());
		assertEquals(2, c.number());
	}

	@Test
	public void testSelection2() {
		Configuration c = new Configuration(fm, true);
		assertTrue(c.valid());
		assertEquals(2, c.number());
	}

	@Test
	public void testSelection3() {
		Configuration c = new Configuration(fm, false);
		c.setManual("A", Selection.SELECTED);
		c.setManual("C", Selection.SELECTED);
		assertTrue(c.valid());
		assertEquals(1, c.number());
	}

	@Test
	public void testSelection4() {
		Configuration c = new Configuration(fm, true);
		c.setManual("A", Selection.SELECTED);
		assertTrue(c.valid());
		assertEquals(1, c.number());
	}

	@Test
	public void testSelection5() {
		Configuration c = new Configuration(fm, true);
		boolean exception = false;
		try {
			c.setManual("B", Selection.SELECTED);
		} catch (SelectionNotPossibleException e) {
			exception = true;
		}
		assertTrue(exception);
	}

	@Test
	public void testNumber1() {
		FeatureModel fm = loadXML("<and name=\"S\">" + "<feature name=\"A\"/>"
				+ "<feature mandatory=\"true\" name=\"B\"/>"
				+ "<feature name=\"C\"/>" + "</and>");
		Configuration c = new Configuration(fm);
		assertEquals(4, c.number());
	}

	@Test
	public void testNumber2() {
		FeatureModel fm = loadXML("<or name=\"S\">" + "<feature name=\"A\"/>"
				+ "<feature name=\"B\"/>" + "<feature name=\"C\"/>" + "</or>");
		Configuration c = new Configuration(fm);
		assertEquals(7, c.number());
	}

	@Test
	public void testNumber3() {
		FeatureModel fm = loadXML("<alt name=\"S\">" + "<feature name=\"A\"/>"
				+ "<feature name=\"B\"/>" + "<feature name=\"C\"/>" + "</alt>");
		Configuration c = new Configuration(fm);
		assertEquals(3, c.number());
	}

	@Test
	public void testNumber4() {
		FeatureModel fm = loadXML("<and name=\"S\">" + "<feature name=\"A\"/>"
				+ "<feature mandatory=\"true\" name=\"B\"/>"
				+ "<feature abstract=\"true\" name=\"C\"/>" + "</and>");
		Configuration c = new Configuration(fm, true, false);
		assertEquals(2, c.number());
	}

	@Test
	public void testNumber5() {
		FeatureModel fm = loadXML("<or name=\"S\">" + "<feature name=\"A\"/>"
				+ "<feature name=\"B\"/>"
				+ "<feature abstract=\"true\" name=\"C\"/>" + "</or>");
		Configuration c = new Configuration(fm, true, false);
		assertEquals(4, c.number());
	}

	@Test
	public void testNumber6() {
		FeatureModel fm = loadXML("<alt name=\"S\">" + "<feature name=\"A\"/>"
				+ "<feature name=\"B\"/>"
				+ "<feature abstract=\"true\" name=\"C\"/>" + "</alt>");
		Configuration c = new Configuration(fm);
		assertEquals(3, c.number());
	}

	private static FeatureModel loadGUIDSL(String grammar) {
		FeatureModel fm = new FeatureModel();
		IFeatureModelReader reader = new GuidslReader(fm);
		try {
			reader.readFromString(grammar);
		} catch (UnsupportedModelException e) {
			assertTrue(false);
		}
		return fm;
	}

	private static FeatureModel loadXML(String xml) {
		xml = "<featureModel><struct>" + xml;
		xml += "</struct></featureModel>";
		FeatureModel fm = new FeatureModel();
		IFeatureModelReader reader = new XmlFeatureModelReader(fm,null);
		try {
			reader.readFromString(xml);
		} catch (UnsupportedModelException e) {
			assertTrue(false);
		}
		return fm;
	}

}
