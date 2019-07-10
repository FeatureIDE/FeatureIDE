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
package de.ovgu.featureide.fm.attributes.tests;

import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import de.ovgu.featureide.fm.attributes.FMAttributesLibrary;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.init.FMCoreLibrary;
import de.ovgu.featureide.fm.core.init.LibraryManager;

/**
 * This class tests the different methods for the {@link ExtendedFeatureModel}.
 * 
 * @author Joshua Sprey
 *
 */
public class TExtendedFeatureModel {

	private static final ExtendedFeatureModelFactory factory = new ExtendedFeatureModelFactory();

	@Before
	public void prepareWorkbench() {
		LibraryManager.registerLibrary(new FMCoreLibrary());
		LibraryManager.registerLibrary(new FMAttributesLibrary());
	}

	/**
	 * Tests the method
	 * {@link ExtendedFeatureModel#createDefaultValues(CharSequence)}
	 */
	@Test
	public void test_createDefaultValues() {
		ExtendedFeatureModel model = factory.create();
		model.createDefaultValues("Test");

		// Get created feature called "Test". That feature should be root
		IFeature rFeature = model.getFeature("Test");
		assertTrue(rFeature instanceof ExtendedFeature);
		assertTrue(rFeature.getStructure().isRoot());
		assertTrue(rFeature.getStructure().isAbstract());
		// Get created feature called "Base". That feature should be the only
		// feature apart from the root.
		IFeature bFeature = model.getFeature("Base");
		assertTrue(bFeature instanceof ExtendedFeature);
		assertTrue(!bFeature.getStructure().isRoot());
	}
}
