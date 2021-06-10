package de.ovgu.featureide.fm.attributes.base.impl;

import java.security.MessageDigest;

import de.ovgu.featureide.fm.attributes.base.AbstractFeatureAttributeFactory;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.editing.FeatureModelObfuscator;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

public class ExtendedFeatureModelObfuscator extends FeatureModelObfuscator {

	private final IFeatureModel orgFeatureModel;
	private IFeatureModel obfuscatedFeatureModel;

	public ExtendedFeatureModelObfuscator(IFeatureModel featureModel) {
		super(featureModel);

		orgFeatureModel = featureModel;
	}

	public ExtendedFeatureModelObfuscator(IFeatureModel featureModel, String salt) {
		super(featureModel, salt);

		orgFeatureModel = featureModel;
	}

	@Override
	public IFeatureModel execute(IMonitor<IFeatureModel> monitor) throws Exception {

		if (!(orgFeatureModel instanceof ExtendedFeatureModel)) {
			return super.execute(monitor);
		}

		digest = MessageDigest.getInstance("SHA-256");
		obfuscatedFeatureModel = factory.create();
		obfuscateStructure(orgFeatureModel.getStructure().getRoot(), null);
		super.obfuscateConstraints();
		return obfuscatedFeatureModel;
	}

	private void obfuscateStructure(IFeatureStructure orgFeatureStructure, IFeature parentFeature) {
		final ExtendedFeature orgFeature = (ExtendedFeature) orgFeatureStructure.getFeature();

		final ExtendedFeature obfuscatedFeature =
			(ExtendedFeature) factory.createFeature(obfuscatedFeatureModel, getObfuscatedFeatureName(orgFeature.getName()));
		final String description = orgFeatureStructure.getFeature().getProperty().getDescription();
		if ((description != null) && !description.isEmpty()) {
			obfuscatedFeature.getProperty().setDescription(getObfuscatedDescription(description));
		}

		final AbstractFeatureAttributeFactory attributeFactory = new FeatureAttributeFactory();

		for (IFeatureAttribute attribute : orgFeature.getAttributes()) {

			IFeatureAttribute obfFeatureAttribute = null;

			String obfAttributeName = getObfuscatedFeatureAttributeName(attribute.getName());

			switch (attribute.getType()) {
			case FeatureAttribute.BOOLEAN:
				obfFeatureAttribute = attributeFactory.createBooleanAttribute(obfuscatedFeature, obfAttributeName, attribute.getUnit(),
						(Boolean) attribute.getValue(), attribute.isRecursive(), attribute.isConfigurable());
				break;
			case FeatureAttribute.DOUBLE:
				obfFeatureAttribute = attributeFactory.createDoubleAttribute(obfuscatedFeature, obfAttributeName, attribute.getUnit(),
						(Double) attribute.getValue(), attribute.isRecursive(), attribute.isConfigurable());
				break;
			case FeatureAttribute.LONG:
				obfFeatureAttribute = attributeFactory.createLongAttribute(obfuscatedFeature, obfAttributeName, attribute.getUnit(),
						(Long) attribute.getValue(), attribute.isRecursive(), attribute.isConfigurable());
				break;
			case FeatureAttribute.STRING:
				obfFeatureAttribute = attributeFactory.createStringAttribute(obfuscatedFeature, obfAttributeName, attribute.getUnit(),
						getObfuscatedStringValue((String) attribute.getValue()), attribute.isRecursive(), attribute.isConfigurable());
			}
			obfuscatedFeature.addAttribute(obfFeatureAttribute);
		}

		obfuscatedFeatureModel.addFeature(obfuscatedFeature);
		final IFeatureStructure obfuscatedFeatureStructure = obfuscatedFeature.getStructure();
		obfuscatedFeatureStructure.setAbstract(orgFeatureStructure.isAbstract());
		obfuscatedFeatureStructure.setMandatory(orgFeatureStructure.isMandatory());
		obfuscatedFeatureStructure.setAND(orgFeatureStructure.isAnd());
		obfuscatedFeatureStructure.setMultiple(orgFeatureStructure.isMultiple());
		obfuscatedFeatureStructure.setHidden(orgFeatureStructure.isHidden());
		if (parentFeature == null) {
			obfuscatedFeatureModel.getStructure().setRoot(obfuscatedFeatureStructure);
		} else {
			parentFeature.getStructure().addChild(obfuscatedFeatureStructure);
		}

		for (final IFeatureStructure orgChildStructure : orgFeatureStructure.getChildren()) {
			obfuscateStructure(orgChildStructure, obfuscatedFeature);
		}
	}

	private String getObfuscatedStringValue(String orgValue) {
		return obfuscate(orgValue, new char[RESULT_LENGTH]);
	}

	private String getObfuscatedFeatureAttributeName(String attributeName) {
		return obfuscate(attributeName, new char[RESULT_LENGTH]);
	}

}
