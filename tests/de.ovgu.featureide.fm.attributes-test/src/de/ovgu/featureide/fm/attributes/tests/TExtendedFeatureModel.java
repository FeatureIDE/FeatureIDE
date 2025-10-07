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
package de.ovgu.featureide.fm.attributes.tests;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotSame;
import static org.junit.Assert.assertTrue;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;

import org.junit.Before;
import org.junit.Test;

import de.ovgu.featureide.fm.attributes.FMAttributesLibrary;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.init.FMCoreLibrary;
import de.ovgu.featureide.fm.core.init.LibraryManager;

/**
 * This class tests the different methods for the {@link ExtendedFeatureModel}.
 * 
 * @author Joshua Sprey
 *
 */
public class TExtendedFeatureModel {

	private static final ExtendedFeatureModelFactory factory = new ExtendedFeatureModelFactory();

	@Before
	public void prepareWorkbench() {
		LibraryManager.registerLibrary(FMCoreLibrary.getInstance());
		LibraryManager.registerLibrary(FMAttributesLibrary.getInstance());
	}

	/**
	 * Tests the method {@link ExtendedFeatureModel#createDefaultValues(CharSequence)}
	 */
	@Test
	public void test_createDefaultValues() {
		ExtendedFeatureModel model = factory.create();
		model.createDefaultValues("Test");

		// Get created feature called "Test". That feature should be root
		IFeature rFeature = model.getFeature("Test");
		assertTrue(rFeature instanceof ExtendedFeature);
		assertTrue(rFeature.getStructure().isRoot());
		assertTrue(rFeature.getStructure().isAbstract());
		// Get created feature called "Base". That feature should be the only
		// feature apart from the root.
		IFeature bFeature = model.getFeature("Base");
		assertTrue(bFeature instanceof ExtendedFeature);
		assertTrue(!bFeature.getStructure().isRoot());
	}

	@Test
	public void testClone() throws IllegalArgumentException, IllegalAccessException {
		ExtendedFeatureModel fm1 = Commons.getPCConfiguratorModel();
		classesUseDifferentMemory(fm1, fm1.clone(true), 0, "fm", new HashSet<>());
	}

	private static final LinkedHashSet<String> unequalFields = new LinkedHashSet<>(Arrays.asList( //
			"de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature#eventManager", //
			"de.ovgu.featureide.fm.core.base.impl.Constraint#eventManager", //
			"de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel#eventManager", //
			"de.ovgu.featureide.fm.core.RenamingsManager#eventManager"));
	private static final LinkedHashSet<String> sameFields = new LinkedHashSet<>(Arrays.asList( //
			"de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel#factoryID", //
			"de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel#factory", //
			"org.prop4j.Literal#var", //
			"id"));
	private static final LinkedHashSet<Class<?>> wrapperClasses =
		new LinkedHashSet<>(Arrays.asList(Double.class, Float.class, Long.class, Integer.class, Short.class, Character.class, Byte.class, Boolean.class));

	private void classesUseDifferentMemory(Object o1, Object o2, int depth, String fieldName, HashSet<Integer> alreadyChecked)
			throws IllegalArgumentException, IllegalAccessException {
		if (o1 == null && o2 == null) {
			return;
		}

		if (!alreadyChecked.add(System.identityHashCode(o1))) {
			return;
		}

		Class<? extends Object> class1 = o1.getClass();
		Class<? extends Object> class2 = o2.getClass();
		assertEquals(class1, class2);

		if (!unequalFields.contains(fieldName)) {
			assertEquals("values for " + fieldName + " are not equal", o1, o2);
		}

		if (class1.isPrimitive() || wrapperClasses.contains(class1)) {
			return;
		}

		if (!sameFields.contains(fieldName)) {
			assertNotSame("values for " + fieldName + " are the same", o1, o2);
		}

		ArrayList<Field> allFields = new ArrayList<>();
		Class<?> fieldClass = class1;
		while (fieldClass != null) {
			Field[] fields = fieldClass.getDeclaredFields();
			allFields.addAll(Arrays.asList(fields));
			fieldClass = fieldClass.getSuperclass();
		}

		for (Field field : allFields) {
			if ((field.getModifiers() & (Modifier.STATIC | Modifier.TRANSIENT)) != 0) {
				continue;
			}
			try {
				field.setAccessible(true);
			} catch (Exception e) {
				continue;
			}
			Object i1 = field.get(o1);
			Object i2 = field.get(o2);
			if (i1 == null && i2 == null) {
				continue;
			}

			String childName = String.format("%s#%s", class1.getName(), field.getName());

			if (Iterable.class.isAssignableFrom(field.getType())) {
				Iterator<?> iterator1 = ((Iterable<?>) i1).iterator();
				Iterator<?> iterator2 = ((Iterable<?>) i2).iterator();
				int i = 0;
				while (iterator1.hasNext()) {
					classesUseDifferentMemory(iterator1.next(), iterator2.next(), depth + 1, childName + i, alreadyChecked);
				}
				assertFalse(iterator2.hasNext());
			} else if (Map.class.isAssignableFrom(field.getType())) {
				Iterator<? extends Map.Entry<?, ?>> iterator1 = ((Map<?, ?>) i1).entrySet().iterator();
				Iterator<? extends Map.Entry<?, ?>> iterator2 = ((Map<?, ?>) i2).entrySet().iterator();
				int i = 0;
				while (iterator1.hasNext()) {
					Entry<?, ?> next1 = iterator1.next();
					Entry<?, ?> next2 = iterator2.next();
					classesUseDifferentMemory(next1.getKey(), next2.getKey(), depth + 1, childName + i + "key", alreadyChecked);
					classesUseDifferentMemory(next1.getValue(), next2.getValue(), depth + 1, childName + i + "value", alreadyChecked);
				}
				assertFalse(iterator2.hasNext());
			} else if (field.getType().isArray()) {
				if (i1 instanceof Object[]) {
					Object[] array1 = (Object[]) i1;
					Object[] array2 = (Object[]) i2;
					assertEquals(array1.length, array2.length);
					for (int i = 0; i < array1.length; i++) {
						classesUseDifferentMemory(array1[i], array2[i], depth + 1, childName + i, alreadyChecked);
					}
				} else {
					assertEquals(i1, i2);
				}
			} else {
				classesUseDifferentMemory(i1, i2, depth + 1, childName, alreadyChecked);
			}
		}
	}

}
