package de.ovgu.featureide.fm.attributes.tests;

import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import de.ovgu.featureide.fm.attributes.base.AbstractFeatureAttributeFactory;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModelFactory;
import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttributeFactory;
import de.ovgu.featureide.fm.attributes.base.impl.StringFeatureAttribute;
import de.ovgu.featureide.fm.attributes.format.XmlExtendedFeatureModelFormat;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;

/**
 * Tests used to verify the correct behavior for the {@link ExtendedFeature}
 * @author Joshua Sprey
 */
public class TExtendedFeatureTests {

	private static final AbstractFeatureAttributeFactory attributeFactory = new FeatureAttributeFactory();
	private static final ExtendedFeatureModelFactory factory = new ExtendedFeatureModelFactory();

	@Before
	public void prepareWorkbench() {
		FMFactoryManager.factoryWorkspaceProvider.getFactoryWorkspace().assignID(XmlExtendedFeatureModelFormat.ID, ExtendedFeatureModelFactory.ID);
		FMFormatManager.getInstance().addExtension(new XmlExtendedFeatureModelFormat());
		FMFactoryManager.getInstance().addExtension(new ExtendedFeatureModelFactory());
	}

	/**
	 * Checks {@link ExtendedFeature#getAttributes()}
	 */
	@Test
	public void test_getAttributes() {
		//Load model from file
		ExtendedFeatureModel model =  Commons.getSandwitchModel();
		ExtendedFeature breadFeature = (ExtendedFeature)model.getFeature("Bread");
		assertTrue(breadFeature.getAttributes() != null);
		assertTrue(breadFeature.getAttributes().size() == 3);
		
		ExtendedFeature hamFeature = (ExtendedFeature)model.getFeature("Ham");
		assertTrue(hamFeature.getAttributes() != null);
		assertTrue(hamFeature.getAttributes().size() == 3);
		
		ExtendedFeature lettuceFeature = (ExtendedFeature)model.getFeature("Lettuce");
		assertTrue(lettuceFeature.getAttributes() != null);
		assertTrue(lettuceFeature.getAttributes().size() == 3);
	}

	/**
	 * Checks {@link ExtendedFeature#addAttribute(IFeatureAttribute)}
	 */
	@Test
	public void test_addAttributes() {
		//Load model from file
		ExtendedFeatureModel model =  Commons.getSandwitchModel();
		//Get a feature
		ExtendedFeature breadFeature = (ExtendedFeature)model.getFeature("Bread");
		//Create an attribute
		IFeatureAttribute attribute = attributeFactory.createStringAttribute(breadFeature, "test", "Test", "Test Value", false, false);
		//Add the attribute to the feature
		assertTrue(breadFeature.getAttributes().size() == 3);
		breadFeature.addAttribute(attribute);
		assertTrue(breadFeature.getAttributes().size() == 4);
		assertTrue(breadFeature.getAttributes().contains(attribute));
	}
	

	/**
	 * Checks {@link ExtendedFeature#removeAttribute(IFeatureAttribute)}
	 */
	@Test
	public void test_removeAttributes() {
		//Load model from file
		ExtendedFeatureModel model =  Commons.getSandwitchModel();
		//Get a feature
		ExtendedFeature breadFeature = (ExtendedFeature)model.getFeature("Bread");
		//Create an attribute
		IFeatureAttribute attribute = attributeFactory.createStringAttribute(breadFeature, "test", "Test", "Test Value", false, false);
		//Add the attribute to the feature
		assertTrue(breadFeature.getAttributes().size() == 3);
		breadFeature.addAttribute(attribute);
		assertTrue(breadFeature.getAttributes().size() == 4);
		assertTrue(breadFeature.getAttributes().contains(attribute));
		breadFeature.removeAttribute(attribute);
		assertTrue(breadFeature.getAttributes().size() == 3);
		assertTrue(!breadFeature.getAttributes().contains(attribute));
	}
	

	/**
	 * Checks {@link ExtendedFeature#clone(IFeatureModel, de.ovgu.featureide.fm.core.base.IFeatureStructure)}
	 */
	@Test
	public void test_clone() {
		IFeatureModel model = factory.createFeatureModel();
		//Get a feature
		ExtendedFeature testFeature = factory.createFeature(model, "Test");

		//Create an attribute
		IFeatureAttribute attribute = attributeFactory.createStringAttribute(testFeature, "test", "Test", "Test Value", true, true);
		//Add the attribute to the feature
		testFeature.addAttribute(attribute);
		
		IFeature cloneF = testFeature.clone(testFeature.getFeatureModel(), testFeature.getStructure());
		
		assertTrue(cloneF instanceof ExtendedFeature);
		ExtendedFeature cloneExF = (ExtendedFeature)cloneF;
		assertTrue(cloneExF.getAttributes().size() == 1);
		IFeatureAttribute attributeClone = cloneExF.getAttributes().get(0);
		assertTrue(attributeClone.getFeature() == cloneExF);
		assertTrue(attributeClone.getName().equals("test"));
		assertTrue(attributeClone instanceof StringFeatureAttribute);
		assertTrue(attributeClone.getType().equals(FeatureAttribute.STRING));
		assertTrue(attributeClone.getUnit().equals("Test"));
		assertTrue(attributeClone.getValue().equals("Test Value"));
		assertTrue(attributeClone.isRecursive());
		assertTrue(attributeClone.isConfigurable());
	}

	/**
	 * Checks {@link ExtendedFeature#isContainingAttribute(IFeatureAttribute)}
	 */
	@Test
	public void test_isContainingAttribute() {
		//Load model from file
		ExtendedFeatureModel model =  Commons.getSandwitchModel();
		//Get a feature
		ExtendedFeature breadFeature = (ExtendedFeature)model.getFeature("Bread");
		
		for (IFeatureAttribute att : breadFeature.getAttributes()) {
			assertTrue(breadFeature.isContainingAttribute(att));
		}
	}
	/**
	 * Checks {@link ExtendedFeature#createTooltip(Object...)}
	 */
	@Test
	public void test_createTooltip() {
		//Load model from file
		ExtendedFeatureModel model =  Commons.getSandwitchModel();
		//Get a feature
		ExtendedFeature breadFeature = (ExtendedFeature)model.getFeature("Bread");
		//Create the tooltip
		String tooltip = breadFeature.createTooltip("");
		assertTrue(tooltip.contains("Inherited Attributes:"));
		assertTrue(tooltip.contains("recursive configureable long Calories = null"));
		assertTrue(tooltip.contains("recursive boolean Organic Food = null"));
		assertTrue(tooltip.contains("recursive double Price = null"));
	}
}
