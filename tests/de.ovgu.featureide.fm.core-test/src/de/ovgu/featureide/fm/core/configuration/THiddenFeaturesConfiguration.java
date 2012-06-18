/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
import java.util.HashSet;

import org.junit.Test;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * Tests about handling of hidden features during configuration
 * 
 * @author Fabian Benduhn
 */
public class THiddenFeaturesConfiguration extends AbstractConfigurationTest {

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.configuration.AbstractConfigurationTest#loadModel()
	 */
	@Override
	FeatureModel loadModel() {
		return null;
	}
	
	
	@Test
	public void testMandatoryHidden() {
		FeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\"><feature hidden=\"true\" mandatory=\"true\" name=\"B\"/></and>");
		Configuration c = new Configuration(fm);
		assertEquals(1, c.number());
		HashSet<Feature> set = new HashSet<Feature>();
		set.add(fm.getFeature("S"));
		set.add(fm.getFeature("B"));
		assertEquals(c.getSelectedFeatures(),set);
	}

	@Test
	public void testOptionalHidden() {
		FeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\"><feature hidden=\"true\" mandatory=\"false\" name=\"B\"/></and>");
		Configuration c = new Configuration(fm);
		assertEquals(1, c.number());
		HashSet<Feature> set = new HashSet<Feature>();
		set.add(fm.getFeature("S"));
		assertEquals(set,c.getSelectedFeatures());
	}
	
	@Test
	public void testAlternativeHidden() {
		FeatureModel fm = loadXML("<alt mandatory=\"true\" name=\"S\"><feature mandatory=\"true\" name=\"A\"/><feature hidden=\"true\" mandatory=\"false\" name=\"B\"/></alt>");
		Configuration c = new Configuration(fm);
		assertEquals(2, c.number());
		HashSet<Feature> set = new HashSet<Feature>();
		set.add(fm.getFeature("S"));
		//set={S}
		assertEquals(set,c.getSelectedFeatures());
		c.setManual("A", Selection.SELECTED);
	
		set.add(fm.getFeature("A"));
		//set={S,A}
		assertEquals(c.getSelectedFeatures(),set);
	}
	@Test
	public void testHidden() {
		FeatureModel fm = loadXML("<and mandatory=\"true\" name=\"S\"><feature hidden=\"true\" mandatory=\"false\" name=\"B\"/></and>");
		Configuration c = new Configuration(fm);
		assertEquals(1, c.number());
		HashSet<Feature> set = new HashSet<Feature>();
		set.add(fm.getFeature("S"));
		assertEquals(set,c.getSelectedFeatures());
		
	}
}
