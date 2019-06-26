package de.ovgu.featureide.fm.attributes.tests;

import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModelFactory;
import de.ovgu.featureide.fm.attributes.format.XmlExtendedFeatureModelFormat;
import de.ovgu.featureide.fm.attributes.outlineentry.AttributeMaximumEntry;
import de.ovgu.featureide.fm.attributes.outlineentry.AttributeMinimumEntry;
import de.ovgu.featureide.fm.attributes.outlineentry.CountAttributeComputation;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;

public class TExtendedOutline {

	@Before
	public void prepareWorkbench() {
		FMFactoryManager.getInstance().getDefaultFactoryWorkspace().assignID(XmlExtendedFeatureModelFormat.ID,
				ExtendedFeatureModelFactory.ID);
		FMFormatManager.getInstance().addExtension(new XmlExtendedFeatureModelFormat());
		FMFactoryManager.getInstance().addExtension(new ExtendedFeatureModelFactory());
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
		AttributeMaximumEntry max = new AttributeMaximumEntry(congf, attributePrice);
		Object valueObject = max.getResult();

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
		AttributeMinimumEntry max = new AttributeMinimumEntry(congf, attributePrice);
		Object valueObject = max.getResult();

		assertTrue(valueObject instanceof Double);
		double value = (double) valueObject;
		assertTrue(value == 1.99d);
	}

	@Test
	public void testCountAttributeComputation() {
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
		CountAttributeComputation max = new CountAttributeComputation(congf, attributePrice);
		Object valueObject = max.calculateCount();

		assertTrue(valueObject instanceof Integer);
		int value = (int) valueObject;
		assertTrue(value == 19);
	}
}
