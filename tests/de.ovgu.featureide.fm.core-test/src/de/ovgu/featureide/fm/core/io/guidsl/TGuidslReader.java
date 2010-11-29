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
package de.ovgu.featureide.fm.core.io.guidsl;

import static org.junit.Assert.*;
import org.junit.Test;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.Feature.GroupType;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * Test class for GuidslReader
 * 
 * @author Fabian Benduhn
 */
public class TGuidslReader {

	static String AND_GROUP_ALL_OPTIONAL = "Root : [Base] :: _Root ; Base : [A] [B] [C] :: _Base ;";
	static String AND_GROUP_A_MANDATORY = "Root : [Base] :: _Root ; Base : A [B] [C] :: _Base ;";
	static String OR_GROUP = "Root : Base* :: _Root ; Base : A	| B	| C ;";
	static String ALTERNATIVE_GROUP = "Root : Base :: _Root; Base : A | B| C ;";

	@Test
	public void testAndGroupAllOptional() throws UnsupportedModelException {
		FeatureModel model = new FeatureModel();
		GuidslReader reader = new GuidslReader(model);

		reader.readFromString(AND_GROUP_ALL_OPTIONAL);
		Feature a = model.getFeature("A");
		Feature base = model.getFeature("Base");
		assertTrue(base.hasGroupType(GroupType.AND));
		assertFalse(a.isMandatory());

	}

	@Test
	public void testAndGroupAMandatory() throws UnsupportedModelException {
		FeatureModel model = new FeatureModel();
		GuidslReader reader = new GuidslReader(model);

		reader.readFromString(AND_GROUP_A_MANDATORY);

		Feature base = model.getFeature("Base");
		Feature a = model.getFeature("A");
		assertTrue(base.hasGroupType(GroupType.AND));
		assertTrue(a.isMandatory());
	}

@Test
	public void testOrGroup() throws UnsupportedModelException {
		FeatureModel model = new FeatureModel();
		GuidslReader reader = new GuidslReader(model);

		reader.readFromString(OR_GROUP);

		Feature base = model.getFeature("Base");
		assertTrue(base.hasGroupType(GroupType.OR));

	}
	@Test
	public void testAlternativeGroup() throws UnsupportedModelException {
		FeatureModel model = new FeatureModel();
		GuidslReader reader = new GuidslReader(model);

		reader.readFromString(ALTERNATIVE_GROUP);

		Feature base = model.getFeature("Base");
		
		assertTrue(base.hasGroupType(GroupType.ALTERNATIVE));
		
	}
}
