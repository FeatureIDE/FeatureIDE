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
import java.util.List;

import org.junit.Test;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Tests about handling of hidden features during configuration
 *
 * @author Fabian Benduhn
 */
public class THiddenFeaturesConfiguration extends AbstractConfigurationTest {

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.configuration.AbstractConfigurationTest#loadModel()
	 */
	@Override
	IFeatureModel loadModel() {
		return null;
	}

	@Test
	public void testMandatoryHidden() {
		final IFeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\"><feature hidden=\"true\" mandatory=\"true\" name=\"B\"/></and>");
		final Configuration c = new Configuration(fm);
		assertEquals(1, c.number());
		final List<IFeature> list = new ArrayList<IFeature>();
		list.add(fm.getFeature("S"));
		list.add(fm.getFeature("B"));
		assertEquals(c.getSelectedFeatures(), list);
	}

	@Test
	public void testOptionalHidden() {
		final IFeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\"><feature hidden=\"true\" mandatory=\"false\" name=\"B\"/></and>");
		final Configuration c = new Configuration(fm);
		assertEquals(1, c.number());
		final List<IFeature> list = new ArrayList<IFeature>();
		list.add(fm.getFeature("S"));
		assertEquals(list, c.getSelectedFeatures());
	}

	@Test
	public void testAlternativeHidden() {
		final IFeatureModel fm = loadXML(
				"<alt mandatory=\"true\" name=\"S\"><feature mandatory=\"true\" name=\"A\"/><feature hidden=\"true\" mandatory=\"true\" name=\"B\"/></alt>");
		final Configuration c = new Configuration(fm);
		assertEquals(2, c.number());
		c.setManual("A", Selection.UNSELECTED);
		final List<IFeature> list = new ArrayList<IFeature>();
		list.add(fm.getFeature("S"));
		list.add(fm.getFeature("B"));
		// set={S,B}
		assertEquals(list, c.getSelectedFeatures());
		c.setManual("A", Selection.SELECTED);
		list.clear();
		list.add(fm.getFeature("S"));
		list.add(fm.getFeature("A"));
		// set={S,A}
		assertEquals(list, c.getSelectedFeatures());
	}

	@Test
	public void testHidden() {
		final IFeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\"><feature hidden=\"true\" mandatory=\"false\" name=\"B\"/></and>");
		final Configuration c = new Configuration(fm);
		assertEquals(1, c.number());
		final List<IFeature> list = new ArrayList<IFeature>();
		list.add(fm.getFeature("S"));
		assertEquals(list, c.getSelectedFeatures());
	}
}
