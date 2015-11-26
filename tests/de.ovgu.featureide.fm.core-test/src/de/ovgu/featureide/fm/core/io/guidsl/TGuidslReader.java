/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.io.guidsl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * Test class of the {@link GuidslReader}.
 *  
 * @author Fabian Benduhn
 */
public class TGuidslReader {
	protected static String AND_GROUP_ALL_OPTIONAL = "Root : [Base] :: _Root ; Base : [A] [B] [C] :: _Base ;";
	protected static String AND_GROUP_A_MANDATORY = "Root : [Base] :: _Root ; Base : A [B] [C] :: _Base ;";
	protected static String OR_GROUP = "Root : Base* :: _Root ;Base : A	| B	| C ;";
	protected static String ALTERNATIVE_GROUP = "Root : Base ;Base : A| B	| C ;";

	protected static String sep = System.getProperty("file.separator");
	
	@Test
	public void testReaderAndGroupAllOptional() throws UnsupportedModelException {
		FeatureModel model = new FeatureModel();
		GuidslReader reader = new GuidslReader(model);

		reader.readFromString(AND_GROUP_ALL_OPTIONAL);
		Feature a = model.getFeature("A");
		Feature base = model.getFeature("Base");
		assertTrue(base.isAnd());
		assertFalse(a.isMandatory());

	}

	@Test
	public void testReaderAndGroupAMandatory() throws UnsupportedModelException {
		FeatureModel model = new FeatureModel();
		GuidslReader reader = new GuidslReader(model);

		reader.readFromString(AND_GROUP_A_MANDATORY);

		Feature base = model.getFeature("Base");
		Feature a = model.getFeature("A");
		assertTrue(base.isAnd());
		assertTrue(a.isMandatory());
	}

	@Test
	public void testReaderOrGroup() throws UnsupportedModelException {
		FeatureModel model = new FeatureModel();
		GuidslReader reader = new GuidslReader(model);

		reader.readFromString(OR_GROUP);

		Feature base = model.getFeature("Base");
		assertTrue(base.isOr());

	}

	@Test
	public void testReaderAlternativeGroup() throws UnsupportedModelException {
		FeatureModel model = new FeatureModel();
		GuidslReader reader = new GuidslReader(model);

		reader.readFromString(ALTERNATIVE_GROUP);

		Feature base = model.getFeature("Base");
		assertTrue(base.isAlternative());

	}
}
