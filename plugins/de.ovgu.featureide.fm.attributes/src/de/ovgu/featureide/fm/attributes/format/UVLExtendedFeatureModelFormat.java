package de.ovgu.featureide.fm.attributes.format;

import de.ovgu.featureide.fm.attributes.base.impl.BooleanFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.DoubleFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedMultiFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedMultiFeatureModelFactory;
import de.ovgu.featureide.fm.attributes.base.impl.LongFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.StringFeatureAttribute;
import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.MultiFeature;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.io.APersistentFormat;
import de.ovgu.featureide.fm.core.io.LazyReader;
import de.ovgu.featureide.fm.core.io.uvl.UVLFeatureModelFormat;

public class UVLExtendedFeatureModelFormat extends UVLFeatureModelFormat {

	public static final String ID = PluginID.PLUGIN_ID + ".format." + UVLExtendedFeatureModelFormat.class.getSimpleName();

	@Override
	public String getName() {
		return "Extended UVL";
	}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public APersistentFormat<IFeatureModel> getInstance() {
		return new UVLExtendedFeatureModelFormat();
	}

	// Override
	// parse Attribute
	// for each(contains constraint) -> parse Attribute (fm, e.getValue())
	// für alle anderen: füg zu attributes des features hinzu.

	@Override
	protected void parseAttribute(MultiFeatureModel fm, MultiFeature feature, String attributeKey, Object attributeValue) {
		if (attributeKey.equals("constraint") || attributeKey.equals("constraints")) {
			super.parseAttribute(fm, feature, attributeKey, attributeValue);
		} else if (!attributeKey.equals("abstract") && !attributeKey.equals(EXTENDED_ATTRIBUTE_NAME)) {
			ExtendedMultiFeature extendedFeature = (ExtendedMultiFeature) feature;
			if (attributeValue instanceof String) {
				extendedFeature.addAttribute(new StringFeatureAttribute(extendedFeature, attributeKey, null, (String) attributeValue, false, false));
			} else if (attributeValue instanceof Double) {
				extendedFeature.addAttribute(new DoubleFeatureAttribute(extendedFeature, attributeKey, null, (Double) attributeValue, false, false));
			} else if (attributeValue instanceof Long) {
				extendedFeature.addAttribute(new LongFeatureAttribute(extendedFeature, attributeKey, null, (Long) attributeValue, false, false));
			} else if (attributeValue instanceof Boolean) {
				extendedFeature.addAttribute(new BooleanFeatureAttribute(extendedFeature, attributeKey, null, (Boolean) attributeValue, false, false));
			}
		}
	}

	@Override
	public boolean supportsContent(CharSequence content) {
		return content.toString().contains(EXTENDED_ATTRIBUTE_NAME);
	}

	@Override
	public boolean supportsContent(LazyReader reader) {
		return supportsContent((CharSequence) reader);
	}

	@Override
	public boolean initExtension() {
		FMFactoryManager.getInstance().getDefaultFactoryWorkspace().assignID(getId(), ExtendedMultiFeatureModelFactory.ID);
		return true;
	}
}
