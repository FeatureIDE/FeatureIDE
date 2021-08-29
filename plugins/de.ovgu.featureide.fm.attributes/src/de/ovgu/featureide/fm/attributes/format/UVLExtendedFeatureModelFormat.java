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

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import clojure.lang.Symbol;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.BooleanFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.DoubleFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedMultiFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedMultiFeatureModel;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedMultiFeatureModelFactory;
import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttribute;
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
 * This class extends {@link UVLFeatureModelFormat} to support usage of attributes in UVL. Reads / writes {@link ExtendedMultiFeatureModel}s in UVL format.
 * Parses / prints {@link FeatureAttribute}s.
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
		// call super.parseAttribute to parse the constraints that are written under a feature
		if (attributeKey.equals("constraint") || attributeKey.equals("constraints")) {
			super.parseAttribute(fm, feature, attributeKey, attributeValue);
		} else if (!attributeKey.equals("abstract") && !attributeKey.equals(EXTENDED_ATTRIBUTE_NAME)) {
			ExtendedMultiFeature extendedFeature = (ExtendedMultiFeature) feature;
			// check whether the attribute has only a simple value or a list as value. When having a list it means that the attribute has more information saved
			// than just its own value.
			if (attributeValue instanceof List<?>) {
				List<?> attributeList = (List<?>) attributeValue;
				if (attributeList.size() == 2 && attributeList.get(1) instanceof Map<?, ?>) {
					// check if the attributes list contains informations of the attribute in FeatureIDE, which are value, unit, recrusive, and/or configurable
					Map<?, ?> attributeMap = (Map<?, ?>) attributeList.get(1);
					Object value = attributeMap.get("value");
					Object unitObj = attributeMap.get("unit");
					String unit = unitObj instanceof String ? (String) unitObj : "";
					Object recursiveObj = attributeMap.get("recursive");
					boolean recursive = recursiveObj instanceof Boolean ? (Boolean) recursiveObj : false;
					Object configurableObj = attributeMap.get("configurable");
					boolean configurable = configurableObj instanceof Boolean ? (Boolean) configurableObj : false;
					if (value == null) {
						// if the attribute has no value from which we can automatically read the type, the type needs to be found
						Object type = attributeMap.get("type");
						createAttribute(extendedFeature, type instanceof String ? (String) type : null, attributeKey, value, unit, recursive, configurable);
					} else {
						createAttribute(extendedFeature, attributeKey, value, unit, recursive, configurable);
					}
				}
			} else {
				createAttribute(extendedFeature, attributeKey, attributeValue, "", false, false);
			}
		}
	}

	/**
	 * This method determines the type of the given attribute and then adds the attribute to the given feature
	 * 
	 * @param feature the feature that contains the attribute
	 * @param key the name of the attribute
	 * @param value the value of the attribute
	 * @param unit the unit of the attribute
	 * @param recursive true if the attribute is recursive, false otherwise
	 * @param configurable true if the attribute is configurable, false otherwise
	 */
	private void createAttribute(ExtendedMultiFeature feature, String key, Object value, String unit, boolean recursive, boolean configurable) {
		String type = null;
		if (value instanceof String) {
			type = "string";
		} else if (value instanceof Double) {
			type = "double";
		} else if (value instanceof Long) {
			type = "long";
		} else if (value instanceof Boolean) {
			type = "boolean";
		}
		createAttribute(feature, type, key, value, unit, recursive, configurable);
	}

	/**
	 * This method adds the given attribute to the given feature.
	 * 
	 * @param feature the feature that contains the attribute
	 * @param type the type of the attribute
	 * @param key the name of the attribute
	 * @param value the value of the attribute
	 * @param unit the unit of the attribute
	 * @param recursive true if the attribute is recursive, false otherwise
	 * @param configurable true if the attribute is configurable, false otherwise
	 */
	private void createAttribute(ExtendedMultiFeature feature, String type, String key, Object value, String unit, boolean recursive, boolean configurable) {
		if (type != null) {
			switch (type) {
			case "string":
				feature.addAttribute(new StringFeatureAttribute(feature, key, unit, (String) value, recursive, configurable));
				break;
			case "double":
				feature.addAttribute(new DoubleFeatureAttribute(feature, key, unit, (Double) value, recursive, configurable));
				break;
			case "long":
				feature.addAttribute(new LongFeatureAttribute(feature, key, unit, (Long) value, recursive, configurable));
				break;
			case "boolean":
				feature.addAttribute(new BooleanFeatureAttribute(feature, key, unit, (Boolean) value, recursive, configurable));
				break;
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
			attributes.put(attr.getName(), printAttribute(attr));
		}
		return attributes;
	}

	/**
	 * This method takes an attribute from the feature model and converts it to an object that can be written to UVL.
	 * 
	 * @param attr the attribute that has to be written to UVL
	 * @return the value of the attribute. This is either simply the value, if the attr has no other information, or a map containing all information of the
	 *         attribute.
	 */
	private Object printAttribute(IFeatureAttribute attr) {
		if (!attr.isConfigurable() && !attr.isRecursive() && (attr.getUnit() == null || attr.getUnit().equals("")) && attr.getValue() != null) {
			return attr.getValue();
		} else {
			Map<Object, Object> attributeMap = new HashMap<>();
			if (attr.isConfigurable()) {
				attributeMap.put(Symbol.create("configurable"), true);
			}
			if (attr.isRecursive()) {
				attributeMap.put(Symbol.create("recursive"), true);
			}
			if (attr.getUnit() != null && !attr.getUnit().equals("")) {
				attributeMap.put(Symbol.create("unit"), attr.getUnit());
			}
			if (attr.getValue() == null) {
				attributeMap.put(Symbol.create("type"), attr.getType());
			} else {
				attributeMap.put(Symbol.create("value"), attr.getValue());
			}
			return attributeMap;
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
