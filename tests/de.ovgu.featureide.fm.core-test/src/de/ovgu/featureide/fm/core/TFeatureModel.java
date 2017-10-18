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
package de.ovgu.featureide.fm.core;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertSame;

import java.util.Collection;
import java.util.LinkedList;

import org.junit.Test;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;

/**
 * Tests for the {@link IFeatureModel}.
 *
 * @author Jens Meinicke
 */
public class TFeatureModel {

	private static final IFeatureModelFactory factory = FMFactoryManager.getDefaultFactory();

	@Test
	public void recordGetFeatureName() {
		final IFeatureModel fm = factory.createFeatureModel();
		final IFeature feature = factory.createFeature(fm, "test_root");
		fm.addFeature(feature);
		fm.getStructure().setRoot(feature.getStructure());
		final IFeature root = fm.getFeature("test_root");
		assertSame(root.getStructure(), fm.getStructure().getRoot());

		final IFeatureModel clonedModel = fm.clone(null);
		final IFeature root2 = clonedModel.getFeature("test_root");

		assertSame(root2.getStructure(), clonedModel.getStructure().getRoot());
	}

	@Test
	public void getFeatureOrderListTest() {
		final IFeatureModel fm = factory.createFeatureModel();
		final Collection<String> expectedOrder = new LinkedList<String>();
		Collection<String> actualOrder = fm.getFeatureOrderList();
		assertEquals(expectedOrder, actualOrder);

		final IFeature root = factory.createFeature(fm, "root");
		fm.addFeature(root);
		fm.getStructure().setRoot(root.getStructure());
		expectedOrder.add(root.getName());
		actualOrder = fm.getFeatureOrderList();
		assertEquals(expectedOrder, actualOrder);

		final IFeature A = factory.createFeature(fm, "A");
		FeatureUtils.addChild(root, A);
		expectedOrder.add(A.getName());
		actualOrder = fm.getFeatureOrderList();
		assertEquals(expectedOrder, actualOrder);

		final IFeature B = factory.createFeature(fm, "B");
		FeatureUtils.addChild(root, B);
		expectedOrder.add(B.getName());
		actualOrder = fm.getFeatureOrderList();
		assertEquals(expectedOrder, actualOrder);

		final IFeature C = factory.createFeature(fm, "C");
		FeatureUtils.addChild(B, C);
		expectedOrder.add(C.getName());
		actualOrder = fm.getFeatureOrderList();
		assertEquals(expectedOrder, actualOrder);
	}

}
