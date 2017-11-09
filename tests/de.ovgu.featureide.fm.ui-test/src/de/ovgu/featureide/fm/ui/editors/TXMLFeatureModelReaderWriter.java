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
package de.ovgu.featureide.fm.ui.editors;

import static org.junit.Assert.assertEquals;

import java.io.FileNotFoundException;

import org.junit.Test;

import de.ovgu.featureide.Commons;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.ui.editors.elements.GraphicalFeatureModel;

/**
 * Class to test the collapse feature of XmlFeatureModelFormat.java
 *
 * @author Christopher Sontag
 * @author Maximilian Kuehl
 */
public class TXMLFeatureModelReaderWriter {

	@Test
	public void testFeatureCollapsed() throws FileNotFoundException, UnsupportedModelException {
		final IFeatureModel fmOrig = Commons.loadTestFeatureModelFromFile("basic.xml");
		final IFeatureModel fmCollapsed = Commons.loadTestFeatureModelFromFile("basic_collapsed.xml");
		final IFeatureModel fmNotCollapsed = Commons.loadTestFeatureModelFromFile("basic_not_collapsed.xml");

		final IGraphicalFeatureModel gFM = new GraphicalFeatureModel(fmOrig);
		gFM.init();

		final IGraphicalFeatureModel gfmCollapsed = new GraphicalFeatureModel(fmCollapsed);
		gfmCollapsed.init();
		for (final IGraphicalFeature feature : gfmCollapsed.getFeatures()) {
			if (feature.getObject().getName().equals("Root")) {
				feature.setCollapsed(true);
			}
		}

		final IGraphicalFeatureModel gfmNotCollapsed = new GraphicalFeatureModel(fmNotCollapsed);
		gfmNotCollapsed.init();
		gfmCollapsed.init();
		for (final IGraphicalFeature feature : gfmCollapsed.getFeatures()) {
			feature.setCollapsed(false);
		}

		assertEquals(gFM.getVisibleFeatures().size(), gfmCollapsed.getFeatures().size());

		int notVisible = 0;
		for (final IGraphicalFeature feature : gfmCollapsed.getFeatures()) {
			if (feature.hasCollapsedParent()) {
				notVisible++;
			}
		}

		assertEquals(gFM.getVisibleFeatures().size(), gfmCollapsed.getVisibleFeatures().size() + notVisible);

		assertEquals(gFM.getVisibleFeatures().size(), gfmNotCollapsed.getVisibleFeatures().size());
	}

}
