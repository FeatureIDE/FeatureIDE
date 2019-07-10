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
