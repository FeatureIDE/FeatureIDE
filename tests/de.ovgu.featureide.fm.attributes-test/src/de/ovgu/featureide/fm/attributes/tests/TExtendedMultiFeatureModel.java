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
package de.ovgu.featureide.fm.attributes.tests;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import de.ovgu.featureide.fm.attributes.FMAttributesLibrary;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedMultiFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedMultiFeatureModel;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedMultiFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.init.FMCoreLibrary;
import de.ovgu.featureide.fm.core.init.LibraryManager;

/**
 * Test for the creation of a default ExtendedMultiFeatureModel
 * 
 * @author Rahel Arens
 * @author Johannes Herschel
 */
public class TExtendedMultiFeatureModel {

	private static final ExtendedMultiFeatureModelFactory factory = new ExtendedMultiFeatureModelFactory();

	@Before
	public void prepareWorkbench() {
		LibraryManager.registerLibrary(FMCoreLibrary.getInstance());
		LibraryManager.registerLibrary(FMAttributesLibrary.getInstance());
	}

	@Test
	public void testCreateDefaultValues() {
		ExtendedMultiFeatureModel model = factory.create();
		model.createDefaultValues("Test");

		IFeatureStructure rootFeatureStructure = model.getStructure().getRoot();
		IFeature rootFeature = rootFeatureStructure.getFeature();
		assertTrue(rootFeature instanceof ExtendedMultiFeature);
		assertTrue(rootFeature.getName().equals("Test"));
		assertTrue(rootFeatureStructure.isAbstract());

		assertEquals(1, rootFeatureStructure.getChildrenCount());
		IFeatureStructure baseFeatureStructure = rootFeatureStructure.getChildren().get(0);
		IFeature baseFeature = baseFeatureStructure.getFeature();
		assertTrue(baseFeature instanceof ExtendedMultiFeature);
		assertTrue(!baseFeatureStructure.isRoot());
		assertFalse(baseFeatureStructure.isAbstract());
		assertEquals(0, baseFeatureStructure.getChildrenCount());
	}
}
