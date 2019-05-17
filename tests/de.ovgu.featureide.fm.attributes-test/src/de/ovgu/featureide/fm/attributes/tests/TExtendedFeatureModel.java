package de.ovgu.featureide.fm.attributes.tests;

import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import de.ovgu.featureide.fm.attributes.base.AbstractFeatureAttributeFactory;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModelFactory;
import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttributeFactory;
import de.ovgu.featureide.fm.attributes.format.XmlExtendedFeatureModelFormat;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;

/**
 * This class tests the different methods for the {@link ExtendedFeatureModel}.
 * @author Joshua Sprey
 *
 */
public class TExtendedFeatureModel {

	private static final AbstractFeatureAttributeFactory attributeFactory = new FeatureAttributeFactory();
	private static final ExtendedFeatureModelFactory factory = new ExtendedFeatureModelFactory();

	@Before
	public void prepareWorkbench() {
		FMFactoryManager.factoryWorkspaceProvider.getFactoryWorkspace().assignID(XmlExtendedFeatureModelFormat.ID, ExtendedFeatureModelFactory.ID);
		FMFormatManager.getInstance().addExtension(new XmlExtendedFeatureModelFormat());
		FMFactoryManager.getInstance().addExtension(new ExtendedFeatureModelFactory());
	}
	
	/**
	 * Tests the method {@link ExtendedFeatureModel#createDefaultValues(CharSequence)}
	 */
	@Test
	public void test_createDefaultValues() {
		ExtendedFeatureModel model = factory.createFeatureModel();
		model.createDefaultValues("Test");
		
		//Get created feature called "Test". That feature should be root
		IFeature rFeature = model.getFeature("Test");
		assertTrue(rFeature instanceof ExtendedFeature);
		assertTrue(rFeature.getStructure().isRoot());
		assertTrue(rFeature.getStructure().isAbstract());
		//Get created feature called "Base". That feature should be the only feature apart from the root.
		IFeature bFeature = model.getFeature("Base");
		assertTrue(bFeature instanceof ExtendedFeature);
		assertTrue(!bFeature.getStructure().isRoot());
	}
}
