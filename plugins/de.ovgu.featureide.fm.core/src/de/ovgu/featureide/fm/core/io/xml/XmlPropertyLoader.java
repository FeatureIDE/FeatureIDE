/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.io.xml;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

import de.ovgu.featureide.fm.core.base.IPropertyContainer;
import de.ovgu.featureide.fm.core.base.IPropertyContainer.Entry;
import de.ovgu.featureide.fm.core.base.IPropertyContainer.Type;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * @author Marcus Pinnecke
 */
public class XmlPropertyLoader {

	public static final String PROPERTIES = "properties";
	public static final String PROPERTY = "property";
	public static final String KEY = "key";
	public static final String VALUE = "value";
	public static final String TYPE = "data-type";
	public static final String FEATURE = "feature";
	public static final String NAME = "name";

	public enum ParserType {
		FEATURE_PROPERTIES_PARSER
	}

	public interface PropertiesParser {

		Set<String> getIdentifier();

		Set<IPropertyContainer.Entry<String, IPropertyContainer.Type, Object>> getPropertyEntries(String featureName);

		ParserType getType();
	}

	class FeaturePropertiesParser implements PropertiesParser {

		private final Map<String, Set<IPropertyContainer.Entry<String, IPropertyContainer.Type, Object>>> featureProperties = new HashMap<>();

		public FeaturePropertiesParser(Element e) {
			parsePropertiesOfFeature(e);
		}

		private void parsePropertiesOfFeature(Element featureNode) {
			if (!featureNode.hasAttribute(NAME)) {
				throw new UnsupportedOperationException("Property container of type feature is missing required name attribute");
			} else {
				final String featureName = featureNode.getAttribute(NAME);
				final Set<IPropertyContainer.Entry<String, IPropertyContainer.Type, Object>> propertyEntries = parsePropertyEntries(featureNode);
				featureProperties.put(featureName, propertyEntries);
			}

		}

		@Override
		public Set<String> getIdentifier() {
			return featureProperties.keySet();
		}

		@Override
		public Set<IPropertyContainer.Entry<String, IPropertyContainer.Type, Object>> getPropertyEntries(String featureName) {
			return featureProperties.get(featureName);
		}

		@Override
		public ParserType getType() {
			return ParserType.FEATURE_PROPERTIES_PARSER;
		}

	}

	private final NodeList propertiesNode;

	public XmlPropertyLoader(NodeList propertiesNode) throws UnsupportedModelException {
		this.propertiesNode = propertiesNode;
	}

	public Collection<PropertiesParser> parseProperties() throws UnsupportedModelException {
		final Collection<PropertiesParser> result = new ArrayList<>();

		for (final Element domainNode : getElements(propertiesNode)) {
			result.addAll(parsePropertiesOfDomain(domainNode.getChildNodes()));
		}

		return result;
	}

	private ArrayList<Element> getElements(NodeList nodeList) {
		final ArrayList<Element> elements = new ArrayList<Element>(nodeList.getLength());
		for (int temp = 0; temp < nodeList.getLength(); temp++) {
			final org.w3c.dom.Node nNode = nodeList.item(temp);
			if (nNode.getNodeType() == org.w3c.dom.Node.ELEMENT_NODE) {
				final Element eElement = (Element) nNode;
				elements.add(eElement);
			}
		}
		return elements;
	}

	private Collection<PropertiesParser> parsePropertiesOfDomain(NodeList domainNode) {
		final List<PropertiesParser> parsers = new ArrayList<>();

		for (final Element e : getElements(domainNode)) {
			final String tagName = e.getTagName();
			if (tagName.equals(FEATURE)) {
				parsers.add(new FeaturePropertiesParser(e));
			} else {
				throw new UnsupportedOperationException("Unkown domain which contains properties. Don't know where to attach them:" + tagName);
			}
		}

		return parsers;
	}

	private Set<Entry<String, Type, Object>> parsePropertyEntries(Element propertyContainerNode) {
		final Set<Entry<String, Type, Object>> result = new HashSet<>();
		final NodeList properties = propertyContainerNode.getElementsByTagName(PROPERTY);
		for (final Element property : getElements(properties)) {
			if (!(property.hasAttribute(KEY) && property.hasAttribute(VALUE) && property.hasAttribute(TYPE))) {
				throw new UnsupportedOperationException("One property of container " + propertyContainerNode.getAttribute(NAME)
					+ " is missing one of the required attributes: " + KEY + ", " + VALUE + "," + TYPE);
			} else {
				final String key = property.getAttribute(KEY);
				final Type type = Type.valueOf(property.getAttribute(TYPE));
				final Object value = castValue(type, property.getAttribute(VALUE));
				final Entry<String, Type, Object> entry = new Entry<String, IPropertyContainer.Type, Object>(key, type, value);
				if (result.contains(entry)) {
					for (final Entry<String, Type, Object> e : result) {
						if (e.equals(entry) && (!(e.getValue().equals(entry.getValue()) && (e.getType().equals(entry.getType()))))) {
							throw new IllegalStateException("Ambigous property definition for key: " + key);
						}
					}
				} else {
					result.add(entry);
				}
			}
		}
		return result;
	}

	private Object castValue(Type type, String value) {
		if ((value == null) || value.trim().isEmpty()) {
			throw new RuntimeException("Property value is not allowed to be empty");
		}
		switch (type) {
		case BOOLEAN:
			return Boolean.valueOf(value);
		case BYTE:
			return Byte.valueOf(value);
		case CHAR:
			return value.charAt(0);
		case DOUBLE:
			return Double.valueOf(value);
		case FLOAT:
			return Float.valueOf(value);
		case INT:
			return Integer.valueOf(value);
		case LONG:
			return Long.valueOf(value);
		case SHORT:
			return Short.valueOf(value);
		case STRING:
			return value;
		default:
			throw new RuntimeException("Unsupported value type for property:" + type);
		}
	}

}
