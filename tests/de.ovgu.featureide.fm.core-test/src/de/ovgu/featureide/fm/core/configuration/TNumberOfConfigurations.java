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
package de.ovgu.featureide.fm.core.configuration;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Tests about the calculation of the number of valid configurations.
 *
 * @author Thomas Thuem
 * @author Fabian Benduhn
 */
public class TNumberOfConfigurations extends AbstractConfigurationTest {

	@Override
	IFeatureModel loadModel() {
		return null;
	}

	@Test
	public void testOnlyRoot() {
		final IFeatureModel fm = loadXML("<feature mandatory=\"true\" name=\"S\"/>");
		final Configuration c = new Configuration(fm);
		assertEquals(1, c.number());
	}

	@Test
	public void testVoidOnlyRoot() {
		final IFeatureModel fm = loadXML("<feature mandatory=\"true\" name=\"S\"/>", "<rule><not><var>S</var></not></rule>");
		final Configuration c = new Configuration(fm);
		assertEquals(0, c.number());
	}

	@Test
	public void testVoidModel() {
		final IFeatureModel fm =
			loadXML("<and mandatory=\"true\" name=\"S\"><feature mandatory=\"true\" name=\"a\"/></and>", "<rule><not><var>a</var></not></rule>");
		final Configuration c = new Configuration(fm);
		assertEquals(0, c.number());
	}

	@Test
	public void testOnlyMandatory() {
		final IFeatureModel fm = loadXML("	<and mandatory=\"true\" name=\"S\">	<feature mandatory=\"true\" name=\"A\"/></and>");
		final Configuration c = new Configuration(fm);
		assertEquals(1, c.number());
	}

	@Test
	public void testOnlyOptional() {
		final IFeatureModel fm = loadXML("	<and mandatory=\"true\" name=\"S\">	<feature mandatory=\"false\" name=\"A\"/></and>");
		final Configuration c = new Configuration(fm);
		assertEquals(2, c.number());
	}

	@Test
	public void testAndGroup() {
		final IFeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\"><feature mandatory=\"true\" name=\"A\"/><feature name=\"B\"/></and>");
		final Configuration c = new Configuration(fm);
		assertEquals(2, c.number());
	}

	@Test
	public void testOnlyOrGroup() {
		final IFeatureModel fm =
			loadXML("<or mandatory=\"true\" name=\"S\"><feature mandatory=\"true\" name=\"A\"/><feature mandatory=\"true\" name=\"B\"/></or>");
		final Configuration c = new Configuration(fm);
		assertEquals(3, c.number());
	}

	// mandatory true/false shouldnt matter in OR group
	@Test
	public void testOnlyOrGroup2() {
		final IFeatureModel fm =
			loadXML("<or mandatory=\"true\" name=\"S\"><feature mandatory=\"false\" name=\"A\"/><feature mandatory=\"false\" name=\"B\"/></or>");
		final Configuration c = new Configuration(fm);
		assertEquals(3, c.number());
	}

	@Test
	public void testAlternativeGroup() {
		final IFeatureModel fm =
			loadXML("<alt mandatory=\"true\" name=\"S\"><feature mandatory=\"true\" name=\"A\"/><feature mandatory=\"true\" name=\"B\"/></alt>");
		final Configuration c = new Configuration(fm);
		assertEquals(2, c.number());
	}

	@Test
	public void testAlternativeGroup2() {
		final IFeatureModel fm = loadXML(
				"<alt mandatory=\"true\" name=\"S\"><feature mandatory=\"true\" name=\"A\"/><feature mandatory=\"true\" name=\"B\"/><feature mandatory=\"true\" name=\"C\"/></alt>");
		final Configuration c = new Configuration(fm);
		assertEquals(3, c.number());
	}

	@Test
	public void testAbstract() {
		final IFeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\"><feature abstract=\"true\" name=\"C\"/></and>");
		final Configuration c = new Configuration(fm, true, true);
		assertEquals(2, c.number());
	}

	@Test
	public void testAbstract2() {
		final IFeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\"><feature abstract=\"true\" name=\"C\"/></and>");
		final Configuration c = new Configuration(fm, true, false);
		assertEquals(1, c.number());
	}

	@Test
	public void testAbstract3() {
		final IFeatureModel fm =
			loadXML("<and mandatory=\"true\" name=\"S\"><feature abstract=\"true\" name=\"A\"/><feature name=\"B\"/><feature name=\"C\"/></and>");
		final Configuration c = new Configuration(fm, true, false);
		assertEquals(4, c.number());
	}

	@Test
	public void testAbstract4() {
		final IFeatureModel fm =
			loadXML("<and mandatory=\"true\" name=\"S\"><feature abstract=\"true\" name=\"A\"/><feature name=\"B\"/><feature name=\"C\"/></and>");
		final Configuration c = new Configuration(fm);
		assertEquals(8, c.number());
	}

	// TODO: replace selection strategy for hidden features
	@Test
	public void testHidden() {
		final IFeatureModel fm =
			loadXML("<and mandatory=\"true\" name=\"S\"><feature mandatory=\"false\" name=\"A\"/><feature hidden=\"true\" name=\"B\"/></and>");
		final Configuration c = new Configuration(fm);
		final long x = c.number();
		assertEquals(2, x);
	}

	@Test
	public void testDependendHidden() {
		final IFeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\">" + "<feature name=\"A\"/>" + "<feature hidden=\"true\" name=\"B\"/>" + "</and>",
				"<rule>" + "<eq>" + "<var>A</var>" + "<var>B</var>" + "</eq>" + "</rule>");
		final Configuration c = new Configuration(fm);
		assertEquals(2, c.number());
	}

	@Test
	public void testWithSimplePositiveConstraint() {
		final IFeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\"><feature name=\"A\"/></and>", "<rule><var>A</var></rule>");
		final Configuration c = new Configuration(fm);
		assertEquals(1, c.number());
	}

	@Test
	public void testWithSimpleNegationConstraint() {
		final IFeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\"><feature name=\"A\"/></and>", "<rule><not><var>A</var></not></rule>");
		final Configuration c = new Configuration(fm);
		assertEquals(1, c.number());

	}

	@Test
	public void testWithImplicationConstraint() {
		final IFeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\"><feature mandatory=\"true\" name=\"A\"/><feature name=\"B\"/></and>",
				"<rule><imp><var>A</var><var>B</var></imp></rule>");
		final Configuration c = new Configuration(fm);
		assertEquals(1, c.number());

	}

	@Test
	public void testWithComplexConstraints() {
		final IFeatureModel fm =
			loadXML("<and mandatory=\"true\" name=\"S\"><feature name=\"A\"/><feature name=\"B\"/><feature name=\"C\"/><feature name=\"D\"/></and>",
					"<rule><disj><var>A</var><imp><var>B</var><eq><var>C</var><not><var>D</var></not></eq></imp></disj></rule>");
		final Configuration c = new Configuration(fm);
		assertEquals(14, c.number());

	}

	@Test
	public void testCombination1() {
		final IFeatureModel fm =
			loadXML("<and name=\"S\">" + "<feature name=\"A\"/>" + "<feature mandatory=\"true\" name=\"B\"/>" + "<feature name=\"C\"/>" + "</and>");
		final Configuration c = new Configuration(fm);
		assertEquals(4, c.number());
	}

	@Test
	public void testCombination2() {
		final IFeatureModel fm = loadXML("<or name=\"S\">" + "<feature name=\"A\"/>" + "<feature name=\"B\"/>" + "<feature name=\"C\"/>" + "</or>");
		final Configuration c = new Configuration(fm);
		assertEquals(7, c.number());
	}

	@Test
	public void testCombination3() {
		final IFeatureModel fm = loadXML("<alt name=\"S\">" + "<feature name=\"A\"/>" + "<feature name=\"B\"/>" + "<feature name=\"C\"/>" + "</alt>");
		final Configuration c = new Configuration(fm);
		assertEquals(3, c.number());
	}

	@Test
	public void testCombination4() {
		final IFeatureModel fm = loadXML("<and name=\"S\">" + "<feature name=\"A\"/>" + "<feature mandatory=\"true\" name=\"B\"/>"
			+ "<feature abstract=\"true\" name=\"C\"/>" + "</and>");
		final Configuration c = new Configuration(fm, true, false);
		assertEquals(2, c.number());
	}

	@Test
	public void testCombination5() {
		final IFeatureModel fm =
			loadXML("<or name=\"S\">" + "<feature name=\"A\"/>" + "<feature name=\"B\"/>" + "<feature abstract=\"true\" name=\"C\"/>" + "</or>");
		final Configuration c = new Configuration(fm, true, false);
		assertEquals(4, c.number());
	}

	@Test
	public void testCombination6() {
		final IFeatureModel fm =
			loadXML("<alt name=\"S\">" + "<feature name=\"A\"/>" + "<feature name=\"B\"/>" + "<feature abstract=\"true\" name=\"C\"/>" + "</alt>");
		final Configuration c = new Configuration(fm);
		assertEquals(3, c.number());
	}

}
