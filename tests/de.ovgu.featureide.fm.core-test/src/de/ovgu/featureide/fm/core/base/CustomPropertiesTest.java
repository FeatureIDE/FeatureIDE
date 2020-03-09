/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.base;

import static org.junit.Assert.fail;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.ovgu.featureide.Commons;
import de.ovgu.featureide.fm.core.base.impl.DefaultFeatureModelFactory;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelFormat;

public class CustomPropertiesTest {

	static final Path modelFile = Paths.get("feature_model_tmp_" + System.currentTimeMillis() + ".xml");
	static final IFeatureModelFactory factory = DefaultFeatureModelFactory.getInstance();

	@Before
	public void setup() {
		CustomFeaturesCustomPropertiesTest.setFileSystem();

		final IFeatureModel model = factory.create();

		final IFeature f1 = factory.createFeature(model, "A");
		final IFeature f2 = factory.createFeature(model, "B");
		final IFeature f3 = factory.createFeature(model, "C");
		final IFeature f4 = factory.createFeature(model, "D");

		f1.getStructure().addChild(f2.getStructure());
		f1.getStructure().addChild(f3.getStructure());
		f3.getStructure().addChild(f4.getStructure());

		model.addFeature(f1);
		model.addFeature(f2);
		model.addFeature(f3);
		model.addFeature(f4);

		model.getFeature("A").getCustomProperties().set("key1", XmlFeatureModelFormat.TYPE_CUSTOM, "value1");
		model.getFeature("B").getCustomProperties().set("key1", XmlFeatureModelFormat.TYPE_CUSTOM, "value1");

		model.getFeature("C").getCustomProperties().set("key2", XmlFeatureModelFormat.TYPE_CUSTOM, "23");
		model.getFeature("C").getCustomProperties().set("key3", XmlFeatureModelFormat.TYPE_CUSTOM, "23");

		model.getStructure().setRoot(f1.getStructure());

		Commons.saveFeatureModel(modelFile, model, new XmlFeatureModelFormat());
	}

	@Test
	public void testCustomProperties() {
		final IFeatureModel model = factory.create();
		final ProblemList problems = Commons.loadFeatureModel(modelFile, model, new XmlFeatureModelFormat());
		Assert.assertFalse(problems.containsError());

		Assert.assertTrue(model.getFeature("A").getCustomProperties().has("key1", XmlFeatureModelFormat.TYPE_CUSTOM));
		Assert.assertTrue(model.getFeature("B").getCustomProperties().has("key1", XmlFeatureModelFormat.TYPE_CUSTOM));
		Assert.assertTrue(model.getFeature("C").getCustomProperties().has("key2", XmlFeatureModelFormat.TYPE_CUSTOM));
		Assert.assertTrue(model.getFeature("C").getCustomProperties().has("key3", XmlFeatureModelFormat.TYPE_CUSTOM));

		Assert.assertFalse(model.getFeature("A").getCustomProperties().has("key2", XmlFeatureModelFormat.TYPE_CUSTOM));
		Assert.assertFalse(model.getFeature("B").getCustomProperties().has("key3", XmlFeatureModelFormat.TYPE_CUSTOM));
		Assert.assertFalse(model.getFeature("C").getCustomProperties().has("key1", XmlFeatureModelFormat.TYPE_CUSTOM));

		Assert.assertTrue((model.getFeature("A").getCustomProperties().get("key1", XmlFeatureModelFormat.TYPE_CUSTOM)).equals("value1"));
		Assert.assertTrue((model.getFeature("B").getCustomProperties().get("key1", XmlFeatureModelFormat.TYPE_CUSTOM)).equals("value1"));
		Assert.assertTrue((model.getFeature("C").getCustomProperties().get("key2", XmlFeatureModelFormat.TYPE_CUSTOM)).equals("23"));
		Assert.assertTrue((model.getFeature("C").getCustomProperties().get("key3", XmlFeatureModelFormat.TYPE_CUSTOM)).equals("23"));

		model.getFeature("A").getCustomProperties().remove("key1", XmlFeatureModelFormat.TYPE_CUSTOM);
		Assert.assertFalse(model.getFeature("A").getCustomProperties().has("key1", XmlFeatureModelFormat.TYPE_CUSTOM));

		try {
			Files.delete(modelFile);
		} catch (final IOException e) {
			e.printStackTrace();
			fail();
		}
		Commons.saveFeatureModel(modelFile, model, new XmlFeatureModelFormat());

		final IFeatureModel model2 = factory.create();
		final ProblemList problems2 = Commons.loadFeatureModel(modelFile, model2, new XmlFeatureModelFormat());

		for (final Problem p : problems2.getErrors()) {
			System.out.println(p.message);
		}

		Assert.assertFalse(problems2.containsError());

		Assert.assertFalse(model2.getFeature("A").getCustomProperties().has("key1", XmlFeatureModelFormat.TYPE_CUSTOM));

	}

	@After
	public void cleanUp() {
		try {
			Files.deleteIfExists(modelFile);
		} catch (final IOException e) {
			e.printStackTrace();
		}
	}

}
