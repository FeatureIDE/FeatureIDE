/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2020  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.attributes.format;

import java.util.Map;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.BooleanFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.DoubleFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedMultiFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedMultiFeatureModelFactory;
import de.ovgu.featureide.fm.attributes.base.impl.LongFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.StringFeatureAttribute;
import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.MultiFeature;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.io.APersistentFormat;
import de.ovgu.featureide.fm.core.io.LazyReader;
import de.ovgu.featureide.fm.core.io.uvl.UVLFeatureModelFormat;

/**
 * Reads / writes extended feature models in UVL format including attributes
 * 
 * @author Johannes Herschel
 * @author Rahel Arens
 */
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
	protected Map<String, Object> printAttributes(IFeature feature) {
		Map<String, Object> attributes = super.printAttributes(feature);
		ExtendedMultiFeature extendedFeature = (ExtendedMultiFeature) feature;
		if (feature.getStructure().isRoot()) {
			attributes.put(EXTENDED_ATTRIBUTE_NAME, true);
		}
		for (IFeatureAttribute attr : extendedFeature.getAttributes()) {
			attributes.put(attr.getName(), attr.getValue());
		}
		return attributes;
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
