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

import java.util.ArrayList;
import java.util.Arrays;

import org.junit.Test;

import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;

/**
 * Tests about handling of hidden features during configuration
 *
 * @author Fabian Benduhn
 */
public class THiddenFeaturesConfiguration extends AbstractConfigurationTest {

	@Override
	IFeatureModel loadModel() {
		return null;
	}

	@Test
	public void testMandatoryHidden() {
		final IFeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\"><feature hidden=\"true\" mandatory=\"true\" name=\"B\"/></and>");
		final Configuration c = new Configuration(new FeatureModelFormula(fm));
		final IConfigurationPropagator propagator = c.getPropagator();
		assertEquals(1L, LongRunningWrapper.runMethod(propagator.number(1000)).longValue());
		LongRunningWrapper.runMethod(propagator.update());
		assertEquals(new ArrayList<>(Arrays.asList(fm.getFeature("S"), fm.getFeature("B"))), c.getSelectedFeatures());
	}

	@Test
	public void testOptionalHidden() {
		final IFeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\"><feature hidden=\"true\" mandatory=\"false\" name=\"B\"/></and>");
		final Configuration c = new Configuration(new FeatureModelFormula(fm));
		final IConfigurationPropagator propagator = c.getPropagator();
		assertEquals(1L, LongRunningWrapper.runMethod(propagator.number(1000)).longValue());
		LongRunningWrapper.runMethod(propagator.update());
		assertEquals(new ArrayList<>(Arrays.asList(fm.getFeature("S"))), c.getSelectedFeatures());
	}

	@Test
	public void testAlternativeHidden() {
		final IFeatureModel fm = loadXML(
				"<alt mandatory=\"true\" name=\"S\"><feature mandatory=\"true\" name=\"A\"/><feature hidden=\"true\" mandatory=\"true\" name=\"B\"/></alt>");
		final Configuration c = new Configuration(new FeatureModelFormula(fm));
		final IConfigurationPropagator propagator = c.getPropagator();
		assertEquals(2L, LongRunningWrapper.runMethod(propagator.number(1000)).longValue());

		// set={S,B}
		c.setManual("A", Selection.UNSELECTED);
		LongRunningWrapper.runMethod(propagator.update());
		assertEquals(new ArrayList<>(Arrays.asList(fm.getFeature("S"), fm.getFeature("B"))), c.getSelectedFeatures());

		// set={S,A}
		c.setManual("A", Selection.SELECTED);
		LongRunningWrapper.runMethod(propagator.update());
		assertEquals(new ArrayList<>(Arrays.asList(fm.getFeature("S"), fm.getFeature("A"))), c.getSelectedFeatures());
	}

	@Test
	public void testHidden() {
		final IFeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\"><feature hidden=\"true\" mandatory=\"false\" name=\"B\"/></and>");
		final Configuration c = new Configuration(new FeatureModelFormula(fm));
		final IConfigurationPropagator propagator = c.getPropagator();
		assertEquals(1L, LongRunningWrapper.runMethod(propagator.number(1000)).longValue());
		LongRunningWrapper.runMethod(propagator.update());
		assertEquals(new ArrayList<>(Arrays.asList(fm.getFeature("S"))), c.getSelectedFeatures());
	}
}
