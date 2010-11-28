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
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.IFeatureModelReader;
import de.ovgu.featureide.fm.core.io.IFeatureModelWriter;
import de.ovgu.featureide.fm.core.io.TAbstractFeatureModelReaderWriter;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * Test class for GuidslReader
 * 
 * @author Fabian Benduhn
 */
public class TGuidslReaderWriter extends TAbstractFeatureModelReaderWriter{
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.io.TAbstractFeatureModelReaderWriter#getWriter()
	 */
	@Override
	protected IFeatureModelWriter getWriter(FeatureModel fm) {
		return new GuidslWriter(fm);
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.io.TAbstractFeatureModelReaderWriter#getReader()
	 */
	@Override
	protected IFeatureModelReader getReader(FeatureModel fm) {
		
		return new GuidslReader(fm);
	}


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
