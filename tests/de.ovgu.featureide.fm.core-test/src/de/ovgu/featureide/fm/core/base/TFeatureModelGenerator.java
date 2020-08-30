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

import org.junit.Test;

import de.ovgu.featureide.fm.core.editing.evaluation.Generator;

/**
 * Tests the feature model generator class: {@link Generator}
 *
 * @author Joshua Sprey
 */
public class TFeatureModelGenerator {

	/**
	 * Test method for {@link Generator#generateFeatureModel(long, int)}.
	 */
	@Test
	public void testModelGenerationWithStaticSeed() {
		final IFeatureModel model = Generator.generateFeatureModel(100, 100);
	}

	/**
	 * Test method for {@link Generator#generateFeatureModel(long, int)}.
	 */
	@Test
	public void testRandomModelGeneration() {
		// Generate five random models
		for (int i = 0; i < 5; i++) {
			try {
				Generator.generateFeatureModel((int) (Math.random() * 100), 100);
			} catch (final Exception e) {
				e.printStackTrace();
				assert false;
			}
		}
	}
}
