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
package de.ovgu.featureide.fm.attributes;

import de.ovgu.featureide.fm.attributes.base.AbstractFeatureAttributeFactory;

/**
 * TODO description
 *
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public class FeatureAttributeTest {

	private static final String MODEL_NAME = "featureAttributes.xml";
	private static final String COMPARISON_MODEL = "featureAttributesCompare.xml";
	private static final String PATH_TO_XML = "./src/testFeatureModels/";
	private static final String TEMP_MODEL = "featureAttributes_model_tmp.xml";

	private static final String FEATURE_HELLO = "HelloWorld";
	private static final String FEATURE_FEATURE = "Feature";
	private static final String FEATURE_WONDERFUL = "Wonderful";
	private static final String FEATURE_BEAUTIFUL = "Beautiful";
	private static final String FEATURE_WORLD = "World";

	private static final String DOUBLE_ATTRIBUTE = "DoubleAttribute";
	private static final String STRING_ATTRIBUTE = "StringAttribute";
	private static final String BOOLEAN_ATTRIBUTE = "BooleanAttribute";
	private static final String LONG_ATTRIBUTE = "LongAttribute";

	private static final String DOUBLE_TYPE = "double";
	private static final String STRING_TYPE = "string";
	private static final String BOOLEAN_TYPE = "boolean";
	private static final String LONG_TYPE = "long";

	private static final Double DOUBLE_VALUE = 6.0;
	private static final String STRING_VALUE = "Hello";
	private static final Boolean BOOLEAN_VALUE = true;
	private static final Long LONG_VALUE = new Long(15);

	private static final String DOUBLE_STRING = "6";
	private static final String BOOLEAN_STRING = "true";
	private static final String LONG_STRING = "15";

	private static final String DOUBLE_UNIT = "Euro";
	private static final String STRING_UNIT = "Dollar";
	private static final String BOOLEAN_UNIT = "Euro";
	private static final String LONG_UNIT = "Euro";

	private static final Boolean FALSE = false;
	private static final Boolean TRUE = true;
	private static final String FALSE_STRING = "false";
	private static final String TRUE_STRING = "true";

	private AbstractFeatureAttributeFactory attributeFactory;

	/*
	 * @Test public void countFeatureAttributes() { final IFeatureModel fm = Commons.loadTestFeatureModelFromFile(MODEL_NAME); for (final IFeature feature :
	 * fm.getFeatures()) { if (feature.getName().equals(FEATURE_HELLO)) { assertEquals(1, feature.getProperty().getAttributes().size()); } if
	 * (feature.getName().equals(FEATURE_FEATURE)) { assertEquals(1, feature.getProperty().getAttributes().size()); } if
	 * (feature.getName().equals(FEATURE_WONDERFUL)) { assertEquals(0, feature.getProperty().getAttributes().size()); } if
	 * (feature.getName().equals(FEATURE_BEAUTIFUL)) { assertEquals(2, feature.getProperty().getAttributes().size()); } if
	 * (feature.getName().equals(FEATURE_WORLD)) { assertEquals(0, feature.getProperty().getAttributes().size()); } } }
	 * @Test public void checkFeatureAttributeTypes() { final IFeatureModel fm = Commons.loadTestFeatureModelFromFile(MODEL_NAME); for (final IFeature feature :
	 * fm.getFeatures()) { if (feature.getName().equals(FEATURE_HELLO)) { assertEquals(DOUBLE_TYPE, feature.getProperty().getAttributes().get(0).getType()); }
	 * if (feature.getName().equals(FEATURE_FEATURE)) { assertEquals(LONG_TYPE, feature.getProperty().getAttributes().get(0).getType()); } if
	 * (feature.getName().equals(FEATURE_BEAUTIFUL)) { assertEquals(STRING_TYPE, feature.getProperty().getAttributes().get(0).getType());
	 * assertEquals(BOOLEAN_TYPE, feature.getProperty().getAttributes().get(1).getType()); } } }
	 * @Test public void checkFeatureAttributeNames() { final IFeatureModel fm = Commons.loadTestFeatureModelFromFile(MODEL_NAME); for (final IFeature feature :
	 * fm.getFeatures()) { if (feature.getName().equals(FEATURE_HELLO)) { assertEquals(DOUBLE_ATTRIBUTE,
	 * feature.getProperty().getAttributes().get(0).getName()); } if (feature.getName().equals(FEATURE_FEATURE)) { assertEquals(LONG_ATTRIBUTE,
	 * feature.getProperty().getAttributes().get(0).getName()); } if (feature.getName().equals(FEATURE_BEAUTIFUL)) { assertEquals(STRING_ATTRIBUTE,
	 * feature.getProperty().getAttributes().get(0).getName()); assertEquals(BOOLEAN_ATTRIBUTE, feature.getProperty().getAttributes().get(1).getName()); } } }
	 * @Test public void checkFeatureAttributeValues() { final IFeatureModel fm = Commons.loadTestFeatureModelFromFile(MODEL_NAME); for (final IFeature feature
	 * : fm.getFeatures()) { if (feature.getName().equals(FEATURE_HELLO)) { assertEquals(DOUBLE_VALUE, feature.getProperty().getAttributes().get(0).getValue());
	 * } if (feature.getName().equals(FEATURE_FEATURE)) { assertEquals(LONG_VALUE, feature.getProperty().getAttributes().get(0).getValue()); } if
	 * (feature.getName().equals(FEATURE_BEAUTIFUL)) { assertEquals(STRING_VALUE, feature.getProperty().getAttributes().get(0).getValue());
	 * assertEquals(BOOLEAN_VALUE, feature.getProperty().getAttributes().get(1).getValue()); } } }
	 * @Test public void checkFeatureAttributeUnits() { final IFeatureModel fm = Commons.loadTestFeatureModelFromFile(MODEL_NAME); for (final IFeature feature :
	 * fm.getFeatures()) { if (feature.getName().equals(FEATURE_HELLO)) { assertEquals(DOUBLE_UNIT, feature.getProperty().getAttributes().get(0).getUnit()); }
	 * if (feature.getName().equals(FEATURE_FEATURE)) { assertEquals(LONG_UNIT, feature.getProperty().getAttributes().get(0).getUnit()); } if
	 * (feature.getName().equals(FEATURE_BEAUTIFUL)) { assertEquals(STRING_UNIT, feature.getProperty().getAttributes().get(0).getUnit());
	 * assertEquals(BOOLEAN_UNIT, feature.getProperty().getAttributes().get(1).getUnit()); } } }
	 * @Test public void checkFeatureAttributeIsConfigurable() { final IFeatureModel fm = Commons.loadTestFeatureModelFromFile(MODEL_NAME); for (final IFeature
	 * feature : fm.getFeatures()) { if (feature.getName().equals(FEATURE_HELLO)) { assertEquals(FALSE,
	 * feature.getProperty().getAttributes().get(0).isConfigurable()); } if (feature.getName().equals(FEATURE_FEATURE)) { assertEquals(FALSE,
	 * feature.getProperty().getAttributes().get(0).isConfigurable()); } if (feature.getName().equals(FEATURE_BEAUTIFUL)) { assertEquals(FALSE,
	 * feature.getProperty().getAttributes().get(0).isConfigurable()); assertEquals(FALSE, feature.getProperty().getAttributes().get(1).isConfigurable()); } } }
	 * @Test public void checkFeatureAttributeAdding() { final File modelFile = new File(TEMP_MODEL); attributeFactory = new FeatureAttributeFactory(); final
	 * IFeatureModel comparisonfm = Commons.loadTestFeatureModelFromFile(COMPARISON_MODEL); final IFeatureAttributeParsedData booleanParsedData = new
	 * FeatureAttributeParsedData(BOOLEAN_ATTRIBUTE, BOOLEAN_TYPE, BOOLEAN_UNIT, BOOLEAN_STRING, FALSE_STRING, FALSE_STRING); final IFeatureAttribute
	 * booleanAttribute = attributeFactory.createFeatureAttribute(booleanParsedData); final IFeatureAttributeParsedData doubleParsedData = new
	 * FeatureAttributeParsedData(DOUBLE_ATTRIBUTE, DOUBLE_TYPE, DOUBLE_UNIT, DOUBLE_STRING, FALSE_STRING, FALSE_STRING); final IFeatureAttribute
	 * doubleAttribute = attributeFactory.createFeatureAttribute(doubleParsedData); final IFeatureAttributeParsedData longParsedData = new
	 * FeatureAttributeParsedData(LONG_ATTRIBUTE, LONG_TYPE, LONG_UNIT, LONG_STRING, FALSE_STRING, FALSE_STRING); final IFeatureAttribute longAttribute =
	 * attributeFactory.createFeatureAttribute(longParsedData); for (final IFeature feature : comparisonfm.getFeatures()) { if
	 * (feature.getName().equals(FEATURE_HELLO)) { feature.getProperty().addAttribute(doubleAttribute); } if (feature.getName().equals(FEATURE_FEATURE)) {
	 * feature.getProperty().addAttribute(longAttribute); } if (feature.getName().equals(FEATURE_BEAUTIFUL)) {
	 * feature.getProperty().addAttribute(booleanAttribute); } } try { SimpleFileHandler.save(modelFile.toPath(), comparisonfm, new XmlFeatureModelFormat());
	 * final DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance(); final DocumentBuilder dBuilder = dbFactory.newDocumentBuilder(); final
	 * Document doc = dBuilder.parse(PATH_TO_XML + MODEL_NAME); final Document docCompare = dBuilder.parse(modelFile); final TransformerFactory tf =
	 * TransformerFactory.newInstance(); final Transformer transformer = tf.newTransformer(); transformer.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION,
	 * "yes"); // Expected final StringWriter writer = new StringWriter(); transformer.transform(new DOMSource(doc), new StreamResult(writer)); final String
	 * xmlString = writer.toString(); // actual final StringWriter writerCompare = new StringWriter(); transformer.transform(new DOMSource(docCompare), new
	 * StreamResult(writerCompare)); final String xmlCompareString = writerCompare.toString(); assertEquals(xmlString, xmlCompareString); modelFile.delete(); }
	 * catch (final Exception e) { throw new RuntimeException(); } }
	 */
}
