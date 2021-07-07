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
package de.ovgu.featureide.fm.core.editing;

import static org.junit.Assert.assertEquals;

import java.io.FileNotFoundException;
import java.util.HashSet;
import java.util.Set;

import org.junit.Test;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.Commons;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * Checks that the calculation of edit categories works properly. A couple of known refactorings, generalizations and arbitrary edits are performed and the
 * result of the ModelComperator is tested.
 *
 * @author Thomas Thuem
 * @author Fabian Benduhn
 * @author Marcus Pinnecke, 01.07.15
 */
public class TModelComparator {

	@Test
	/**
	 * Based on https://github.com/tthuem/FeatureIDE/issues/264
	 *
	 * @author Marcus Pinnecke
	 *
	 */
	public void testForFeatureIDEaddedProducts() throws FileNotFoundException, UnsupportedModelException, TimeoutException {
		final IFeatureModel fm = Commons.loadBenchmarkFeatureModelFromFile("issue_264_model_optional.xml");
		final IFeatureModel fmGen = Commons.loadBenchmarkFeatureModelFromFile("issue_264_model_alternative.xml");
		final ModelComparator comparator = new ModelComparator(1000000);
		final Comparison comparison = comparator.compare(fm, fmGen);

		assertEquals(Comparison.GENERALIZATION, comparison);

		final Set<String> addedProducts = new HashSet<String>();

		Configuration c;
		while ((c = comparator.calculateExample(true)) != null) {
			System.out.println(c);
			addedProducts.add(c.toString());
		}
		// TODO: assertEquals(12, addedProducts.size());
	}
}
