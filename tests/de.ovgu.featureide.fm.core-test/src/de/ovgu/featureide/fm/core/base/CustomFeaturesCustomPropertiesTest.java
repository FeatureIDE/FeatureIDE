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
package de.ovgu.featureide.fm.core.base;

import java.io.File;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IPropertyContainer.Type;
import de.ovgu.featureide.fm.core.base.impl.AFeature;
import de.ovgu.featureide.fm.core.base.impl.Constraint;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FeatureModel;
import de.ovgu.featureide.fm.core.io.FileSystem;
import de.ovgu.featureide.fm.core.io.JavaFileSystem;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelFormat;

public class CustomFeaturesCustomPropertiesTest {

	static class MyFeatureImplementation extends AFeature {

		public MyFeatureImplementation(IFeatureModel featureModel, String name) {
			super(featureModel, name);
		}

		@Override
		public IFeature clone(IFeatureModel newFeatureModel, IFeatureStructure newStructure) {
			throw new RuntimeException();
		}
	}

	static class MyFeatureModelFactoryImplementation implements IFeatureModelFactory {

		public final String ID = MyFeatureModelFactoryImplementation.class.getName();

		@Override
		public String getId() {
			return ID;
		}

		@Override
		public boolean initExtension() {
			return true;
		}

		@Override
		public IConstraint createConstraint(IFeatureModel featureModel, Node propNode) {
			return new Constraint(featureModel, propNode);
		}

		@Override
		public IFeature createFeature(IFeatureModel featureModel, String name) {
			return new MyFeatureImplementation(featureModel, name);
		}

		@Override
		public IFeatureModel createFeatureModel() {
			return new FeatureModel(ID);
		}

	}

	static final File modelFile = new File("feature_model_tmp_" + System.currentTimeMillis() + ".xml");
	static final IFeatureModelFactory factory = new MyFeatureModelFactoryImplementation();

	public static void setFileSystem() {
		// TODO find better solution for setting JavaFileSystem under testing circumstances
		FileSystem.INSTANCE = new JavaFileSystem();
	}

	@Before
	public void setup() throws Throwable {
		setFileSystem();

		FMFactoryManager.getInstance().addExtension(factory);

		final IFeatureModel model = factory.createFeatureModel();

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

		model.getFeature("A").getCustomProperties().set("key1", Type.STRING, "value1");
		model.getFeature("B").getCustomProperties().set("key1", Type.STRING, "value1");

		model.getFeature("C").getCustomProperties().set("key2", Type.INT, 23);
		model.getFeature("C").getCustomProperties().set("key3", Type.INT, 23);

		model.getStructure().setRoot(f1.getStructure());

		Assert.assertTrue(f1 instanceof MyFeatureImplementation);
		Assert.assertTrue(f2 instanceof MyFeatureImplementation);
		Assert.assertTrue(f3 instanceof MyFeatureImplementation);
		Assert.assertTrue(f4 instanceof MyFeatureImplementation);

		final ProblemList problems = SimpleFileHandler.save(modelFile.toPath(), model, new XmlFeatureModelFormat());
		Assert.assertFalse(problems.getErrors().toString(), problems.containsError());
	}

	@Test
	public void testCustomProperties() {
		final IFeatureModel model = factory.createFeatureModel();
		final ProblemList problems = SimpleFileHandler.load(modelFile.toPath(), model, new XmlFeatureModelFormat());
		Assert.assertFalse(problems.getErrors().toString(), problems.containsError());

		System.out.println(model.getFeature("A").getClass().getName());

		Assert.assertTrue(model.getFeature("A") instanceof MyFeatureImplementation);
		Assert.assertTrue(model.getFeature("B") instanceof MyFeatureImplementation);
		Assert.assertTrue(model.getFeature("C") instanceof MyFeatureImplementation);
		Assert.assertTrue(model.getFeature("D") instanceof MyFeatureImplementation);

		Assert.assertTrue(model.getFeature("A").getCustomProperties().has("key1"));
		Assert.assertTrue(model.getFeature("B").getCustomProperties().has("key1"));
		Assert.assertTrue(model.getFeature("C").getCustomProperties().has("key2"));
		Assert.assertTrue(model.getFeature("C").getCustomProperties().has("key3"));

		Assert.assertFalse(model.getFeature("A").getCustomProperties().has("key2"));
		Assert.assertFalse(model.getFeature("B").getCustomProperties().has("key3"));
		Assert.assertFalse(model.getFeature("C").getCustomProperties().has("key1"));

		Assert.assertTrue(model.getFeature("A").getCustomProperties().getDataType("key1").equals(Type.STRING));
		Assert.assertTrue(model.getFeature("B").getCustomProperties().getDataType("key1").equals(Type.STRING));
		Assert.assertTrue(model.getFeature("C").getCustomProperties().getDataType("key2").equals(Type.INT));
		Assert.assertTrue(model.getFeature("C").getCustomProperties().getDataType("key3").equals(Type.INT));

		Assert.assertTrue(((String) model.getFeature("A").getCustomProperties().get("key1")).equals("value1"));
		Assert.assertTrue(((String) model.getFeature("B").getCustomProperties().get("key1")).equals("value1"));
		Assert.assertTrue(((Integer) model.getFeature("C").getCustomProperties().get("key2")).equals(23));
		Assert.assertTrue(((Integer) model.getFeature("C").getCustomProperties().get("key3")).equals(23));

		model.getFeature("A").getCustomProperties().remove("key1");
		Assert.assertFalse(model.getFeature("A").getCustomProperties().has("key1"));

		modelFile.delete();
		SimpleFileHandler.save(modelFile.toPath(), model, new XmlFeatureModelFormat());

		final IFeatureModel model2 = factory.createFeatureModel();
		final ProblemList problems2 = SimpleFileHandler.load(modelFile.toPath(), model2, new XmlFeatureModelFormat());

		for (final Problem p : problems2.getErrors()) {
			System.out.println(p.message);
		}

		Assert.assertFalse(problems2.containsError());

		Assert.assertFalse(model2.getFeature("A").getCustomProperties().has("key1"));
	}

	@After
	public void cleanUp() {
		modelFile.delete();
	}

}
