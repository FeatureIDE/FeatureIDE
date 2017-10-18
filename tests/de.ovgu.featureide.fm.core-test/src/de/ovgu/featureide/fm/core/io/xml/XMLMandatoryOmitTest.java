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
package de.ovgu.featureide.fm.core.io.xml;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.Feature;
import de.ovgu.featureide.fm.core.base.impl.FeatureModel;

/**
 * Class to test that the attribute mandatory is not written into the xml when the feature is part of an OR / ALTERNATIVE group
 *
 * @author Joshua Sprey
 */
public class XMLMandatoryOmitTest {

	@Test
	public void testOmmitingMandatoryAttribute() {
		final XmlFeatureModelFormat format = new XmlFeatureModelFormat();

		// Create new Feature Model
		final IFeatureModel fm = new FeatureModel("OmitTest");

		// Create root
		final IFeature root = new Feature(fm, "Root");
		fm.getStructure().setRoot(root.getStructure());

		// Create Or Group
		final IFeature or = new Feature(fm, "OrGroup");
		root.getStructure().addChild(or.getStructure());

		final IFeature orOne = new Feature(fm, "OrChild");
		orOne.getStructure().setMandatory(true);
		or.getStructure().addChild(orOne.getStructure());
		final IFeature orTwo = new Feature(fm, "OrChild2");
		orTwo.getStructure().setMandatory(true);
		or.getStructure().addChild(orTwo.getStructure());

		// Change or feature to group mode OR
		or.getStructure().changeToOr();

		// Create Alternative Group
		final IFeature alt = new Feature(fm, "AlternativeGroup");
		root.getStructure().addChild(alt.getStructure());

		final IFeature altOne = new Feature(fm, "AlternativeChild");
		altOne.getStructure().setMandatory(true);
		alt.getStructure().addChild(altOne.getStructure());
		final IFeature altTwo = new Feature(fm, "AlternativeChild2");
		altTwo.getStructure().setMandatory(true);
		alt.getStructure().addChild(altTwo.getStructure());

		// Change alternative feature to group mode ALTERNATIVE
		alt.getStructure().changeToAlternative();

		// Create XML from feature model
		String ausgabe = format.write(fm);

		// Replace roots mandatory
		ausgabe = ausgabe.replaceFirst("mandatory=\"true\"", "");

		// Check if mandatory = true is present in current xml
		final boolean isMandantoryPresent = ausgabe.contains("mandatory=\"true\"");

		assertEquals(isMandantoryPresent, false);
	}
}
