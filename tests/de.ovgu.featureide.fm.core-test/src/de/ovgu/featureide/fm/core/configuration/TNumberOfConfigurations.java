/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import java.math.BigInteger;

import org.junit.Test;

import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
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

	private BigInteger number(final IFeatureModel fm, boolean removeAbstract) {
		final FeatureModelFormula featureModel = new FeatureModelFormula(fm);
		final ConfigurationAnalyzer analyzer = new ConfigurationAnalyzer(featureModel, new Configuration(featureModel));
		analyzer.setIncludeAbstractFeatures(!removeAbstract);
		return analyzer.number();
	}

	@Test
	public void testOnlyRoot() {
		final IFeatureModel fm = loadXML("<feature mandatory=\"true\" name=\"S\"/>");
		assertEquals(1, number(fm, false));
	}

	@Test
	public void testVoidOnlyRoot() {
		final IFeatureModel fm = loadXML("<feature mandatory=\"true\" name=\"S\"/>", "<rule><not><var>S</var></not></rule>");
		assertEquals(0, number(fm, false));
	}

	@Test
	public void testVoidModel() {
		final IFeatureModel fm =
			loadXML("<and mandatory=\"true\" name=\"S\"><feature mandatory=\"true\" name=\"a\"/></and>", "<rule><not><var>a</var></not></rule>");
		assertEquals(0, number(fm, false));
	}

	@Test
	public void testOnlyMandatory() {
		final IFeatureModel fm = loadXML("	<and mandatory=\"true\" name=\"S\">	<feature mandatory=\"true\" name=\"A\"/></and>");
		assertEquals(1, number(fm, false));
	}

	@Test
	public void testOnlyOptional() {
		final IFeatureModel fm = loadXML("	<and mandatory=\"true\" name=\"S\">	<feature mandatory=\"false\" name=\"A\"/></and>");
		assertEquals(2, number(fm, false));
	}

	@Test
	public void testAndGroup() {
		final IFeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\"><feature mandatory=\"true\" name=\"A\"/><feature name=\"B\"/></and>");
		assertEquals(2, number(fm, false));
	}

	@Test
	public void testOnlyOrGroup() {
		final IFeatureModel fm =
			loadXML("<or mandatory=\"true\" name=\"S\"><feature mandatory=\"true\" name=\"A\"/><feature mandatory=\"true\" name=\"B\"/></or>");
		assertEquals(3, number(fm, false));
	}

	// mandatory true/false shouldnt matter in OR group
	@Test
	public void testOnlyOrGroup2() {
		final IFeatureModel fm =
			loadXML("<or mandatory=\"true\" name=\"S\"><feature mandatory=\"false\" name=\"A\"/><feature mandatory=\"false\" name=\"B\"/></or>");
		assertEquals(3, number(fm, false));
	}

	@Test
	public void testAlternativeGroup() {
		final IFeatureModel fm =
			loadXML("<alt mandatory=\"true\" name=\"S\"><feature mandatory=\"true\" name=\"A\"/><feature mandatory=\"true\" name=\"B\"/></alt>");
		assertEquals(2, number(fm, false));
	}

	@Test
	public void testAlternativeGroup2() {
		final IFeatureModel fm = loadXML(
				"<alt mandatory=\"true\" name=\"S\"><feature mandatory=\"true\" name=\"A\"/><feature mandatory=\"true\" name=\"B\"/><feature mandatory=\"true\" name=\"C\"/></alt>");
		assertEquals(3, number(fm, false));
	}

	@Test
	public void testAbstract() {
		final IFeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\"><feature abstract=\"true\" name=\"C\"/></and>");
		assertEquals(2, number(fm, false));
	}

	@Test
	public void testAbstract2() {
		final IFeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\"><feature abstract=\"true\" name=\"C\"/></and>");
		assertEquals(1, number(fm, true));
	}

	@Test
	public void testAbstract3() {
		final IFeatureModel fm =
			loadXML("<and mandatory=\"true\" name=\"S\"><feature abstract=\"true\" name=\"A\"/><feature name=\"B\"/><feature name=\"C\"/></and>");
		assertEquals(4, number(fm, true));
	}

	@Test
	public void testAbstract4() {
		final IFeatureModel fm =
			loadXML("<and mandatory=\"true\" name=\"S\"><feature abstract=\"true\" name=\"A\"/><feature name=\"B\"/><feature name=\"C\"/></and>");
		assertEquals(8, number(fm, false));
	}

	// TODO: replace selection strategy for hidden features
	@Test
	public void testHidden() {
		final IFeatureModel fm =
			loadXML("<and mandatory=\"true\" name=\"S\"><feature mandatory=\"false\" name=\"A\"/><feature hidden=\"true\" name=\"B\"/></and>");
		assertEquals(2, number(fm, false));
	}

	@Test
	public void testDependendHidden() {
		final IFeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\">" + "<feature name=\"A\"/>" + "<feature hidden=\"true\" name=\"B\"/>" + "</and>",
				"<rule>" + "<eq>" + "<var>A</var>" + "<var>B</var>" + "</eq>" + "</rule>");
		assertEquals(2, number(fm, false));
	}

	@Test
	public void testWithSimplePositiveConstraint() {
		final IFeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\"><feature name=\"A\"/></and>", "<rule><var>A</var></rule>");
		assertEquals(1, number(fm, false));
	}

	@Test
	public void testWithSimpleNegationConstraint() {
		final IFeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\"><feature name=\"A\"/></and>", "<rule><not><var>A</var></not></rule>");
		assertEquals(1, number(fm, false));

	}

	@Test
	public void testWithImplicationConstraint() {
		final IFeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\"><feature mandatory=\"true\" name=\"A\"/><feature name=\"B\"/></and>",
				"<rule><imp><var>A</var><var>B</var></imp></rule>");
		assertEquals(1, number(fm, false));

	}

	@Test
	public void testWithComplexConstraints() {
		final IFeatureModel fm =
			loadXML("<and mandatory=\"true\" name=\"S\"><feature name=\"A\"/><feature name=\"B\"/><feature name=\"C\"/><feature name=\"D\"/></and>",
					"<rule><disj><var>A</var><imp><var>B</var><eq><var>C</var><not><var>D</var></not></eq></imp></disj></rule>");
		assertEquals(14, number(fm, false));

	}

	@Test
	public void testCombination1() {
		final IFeatureModel fm =
			loadXML("<and name=\"S\">" + "<feature name=\"A\"/>" + "<feature mandatory=\"true\" name=\"B\"/>" + "<feature name=\"C\"/>" + "</and>");
		assertEquals(4, number(fm, false));
	}

	@Test
	public void testCombination2() {
		final IFeatureModel fm = loadXML("<or name=\"S\">" + "<feature name=\"A\"/>" + "<feature name=\"B\"/>" + "<feature name=\"C\"/>" + "</or>");
		assertEquals(7, number(fm, false));
	}

	@Test
	public void testCombination3() {
		final IFeatureModel fm = loadXML("<alt name=\"S\">" + "<feature name=\"A\"/>" + "<feature name=\"B\"/>" + "<feature name=\"C\"/>" + "</alt>");
		assertEquals(3, number(fm, false));
	}

	@Test
	public void testCombination4() {
		final IFeatureModel fm = loadXML("<and name=\"S\">" + "<feature name=\"A\"/>" + "<feature mandatory=\"true\" name=\"B\"/>"
			+ "<feature abstract=\"true\" name=\"C\"/>" + "</and>");
		assertEquals(2, number(fm, true));
	}

	@Test
	public void testCombination5() {
		final IFeatureModel fm =
			loadXML("<or name=\"S\">" + "<feature name=\"A\"/>" + "<feature name=\"B\"/>" + "<feature abstract=\"true\" name=\"C\"/>" + "</or>");
		assertEquals(4, number(fm, true));
	}

	@Test
	public void testCombination6() {
		final IFeatureModel fm =
			loadXML("<alt name=\"S\">" + "<feature name=\"A\"/>" + "<feature name=\"B\"/>" + "<feature abstract=\"true\" name=\"C\"/>" + "</alt>");
		assertEquals(3, number(fm, false));
	}

}
