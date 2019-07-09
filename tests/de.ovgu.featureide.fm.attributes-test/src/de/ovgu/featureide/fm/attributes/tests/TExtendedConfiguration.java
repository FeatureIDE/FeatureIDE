package de.ovgu.featureide.fm.attributes.tests;

import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedConfigurationFactory;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModelFactory;
import de.ovgu.featureide.fm.attributes.computations.impl.EstimatedMaximumComputation;
import de.ovgu.featureide.fm.attributes.computations.impl.EstimatedMinimumComputation;
import de.ovgu.featureide.fm.attributes.config.ExtendedConfiguration;
import de.ovgu.featureide.fm.attributes.config.ExtendedSelectableFeature;
import de.ovgu.featureide.fm.attributes.format.XmlExtendedConfFormat;
import de.ovgu.featureide.fm.attributes.format.XmlExtendedFeatureModelFormat;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.base.impl.ConfigurationFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;

public class TExtendedConfiguration {

	private static final ExtendedFeatureModelFactory factory = new ExtendedFeatureModelFactory();

	@Before
	public void prepareWorkbench() {
		FMFormatManager.getInstance().addExtension(new XmlExtendedFeatureModelFormat());
		ConfigFormatManager.getInstance().addExtension(new XmlExtendedConfFormat());
		FMFactoryManager.getInstance().addExtension(new ExtendedFeatureModelFactory());
		ConfigurationFactoryManager.getInstance().addExtension(new ExtendedConfigurationFactory());
	}

	@Test
	public void testExtendedSelectableFeature() {
		ExtendedFeatureModel model = factory.create();
		model.createDefaultValues("Test");
		ExtendedConfiguration congf = new ExtendedConfiguration(new FeatureModelFormula(model));

		// Check if selectable features are generated as extended selectable features
		for (SelectableFeature feat : congf.getFeatures()) {
			assertTrue(feat instanceof ExtendedSelectableFeature);

			ExtendedSelectableFeature eFeatu = (ExtendedSelectableFeature) feat;
			eFeatu.addConfigurableAttribute("price", "10");

			assertTrue(eFeatu.getConfigurableAttributes().size() == 1);
			assertTrue(eFeatu.getConfigurableAttributes().get("price") == "10");

			ExtendedSelectableFeature copyTest = new ExtendedSelectableFeature(feat.getFeature());
			copyTest.cloneProperties(eFeatu);

			assertTrue(copyTest.getConfigurableAttributes().size() == 1);
			assertTrue(copyTest.getConfigurableAttributes().get("price") == "10");
		}
	}

	@Test
	public void testMaximumEstimationComputationDouble() {
		ExtendedFeatureModel model = Commons.getSandwitchModel();
		Configuration congf = new Configuration(new FeatureModelFormula(model));

		for (final SelectableFeature f : congf.getFeatures()) {
			if (f.getFeature().getName().equals("Full Grain ")) {
				congf.setManual(f, Selection.SELECTED);
			}
		}

		// Get attribute to compute
		ExtendedFeature feature = (ExtendedFeature) model.getStructure().getRoot().getFeature();
		IFeatureAttribute attributePrice = null;
		for (IFeatureAttribute att : feature.getAttributes()) {
			if (att.getName().equals("Price")) {
				attributePrice = att;
			}
		}

		assertTrue(attributePrice != null);

		// maximum
		EstimatedMaximumComputation max = new EstimatedMaximumComputation(congf, attributePrice);
		Object valueObject = max.getEstimatedMaximum();

		assertTrue(valueObject instanceof Double);
		double value = (double) valueObject;
		assertTrue(value == 8.7d);
	}

	@Test
	public void testMinimumEstimationComputationDouble() {
		ExtendedFeatureModel model = Commons.getSandwitchModel();
		Configuration congf = new Configuration(new FeatureModelFormula(model));

		for (final SelectableFeature f : congf.getFeatures()) {
			if (f.getFeature().getName().equals("Full Grain ")) {
				congf.setManual(f, Selection.SELECTED);
			}
		}

		// Get attribute to compute
		ExtendedFeature feature = (ExtendedFeature) model.getStructure().getRoot().getFeature();
		IFeatureAttribute attributePrice = null;
		for (IFeatureAttribute att : feature.getAttributes()) {
			if (att.getName().equals("Price")) {
				attributePrice = att;
			}
		}

		assertTrue(attributePrice != null);

		// maximum
		EstimatedMinimumComputation max = new EstimatedMinimumComputation(congf, attributePrice);
		Object valueObject = max.getEstimatedMinimum();

		assertTrue(valueObject instanceof Double);
		double value = (double) valueObject;
		assertTrue(value == 1.99d);
	}

	/**
	 * The tests computes the maximum of a long attribute. The result is still
	 * returned in java as double.
	 */
	@Test
	public void testMaximumEstimationComputationLong() {
		ExtendedFeatureModel model = Commons.getSandwitchModel();
		Configuration congf = new Configuration(new FeatureModelFormula(model));

		for (final SelectableFeature f : congf.getFeatures()) {
			if (f.getFeature().getName().equals("Full Grain ")) {
				congf.setManual(f, Selection.SELECTED);
			}
		}

		// Get attribute to compute
		ExtendedFeature feature = (ExtendedFeature) model.getStructure().getRoot().getFeature();
		IFeatureAttribute attributePrice = null;
		for (IFeatureAttribute att : feature.getAttributes()) {
			if (att.getName().equals("Calories")) {
				attributePrice = att;
			}
		}

		assertTrue(attributePrice != null);

		// maximum
		EstimatedMaximumComputation max = new EstimatedMaximumComputation(congf, attributePrice);
		Object valueObject = max.getEstimatedMaximum();

		assertTrue(valueObject instanceof Double);
		Double value = (Double) valueObject;
		assertTrue(value == 679);
	}

	/**
	 * The tests computes the minimum of a long attribute. The result is still
	 * returned in java as double.
	 */
	@Test
	public void testMinimumEstimationComputationLong() {
		ExtendedFeatureModel model = Commons.getSandwitchModel();
		Configuration congf = new Configuration(new FeatureModelFormula(model));

		for (final SelectableFeature f : congf.getFeatures()) {
			if (f.getFeature().getName().equals("Full Grain ")) {
				congf.setManual(f, Selection.SELECTED);
			}
		}

		// Get attribute to compute
		ExtendedFeature feature = (ExtendedFeature) model.getStructure().getRoot().getFeature();
		IFeatureAttribute attributePrice = null;
		for (IFeatureAttribute att : feature.getAttributes()) {
			if (att.getName().equals("Calories")) {
				attributePrice = att;
			}
		}

		assertTrue(attributePrice != null);

		// maximum
		EstimatedMinimumComputation max = new EstimatedMinimumComputation(congf, attributePrice);
		Object valueObject = max.getEstimatedMinimum();

		assertTrue(valueObject instanceof Double);
		Double value = (Double) valueObject;
		assertTrue(value == 203);
	}
}
