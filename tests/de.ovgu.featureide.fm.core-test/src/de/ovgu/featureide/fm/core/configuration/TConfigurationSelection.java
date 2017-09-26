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
package de.ovgu.featureide.fm.core.configuration;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Tests about feature selection.
 *
 * @author Fabian Benduhn
 */
public class TConfigurationSelection extends AbstractConfigurationTest {

	@Override
	IFeatureModel loadModel() {
		return loadGUIDSL("S : [A] [B] C :: _S; %% not B;");
	}

	@Test
	public void testSelection1() {
		final Configuration c = new Configuration(fm, true);
		c.setManual("C", Selection.SELECTED);
		assertTrue(c.isValid());
		assertEquals(2, c.number());
	}

	@Test
	public void testSelection2() {
		final Configuration c = new Configuration(fm, true);
		assertTrue(c.isValid());
		assertEquals(2, c.number());
	}

	@Test
	public void testSelection3() {
		final Configuration c = new Configuration(fm, true);
		c.setManual("A", Selection.SELECTED);
		c.setManual("C", Selection.SELECTED);
		assertTrue(c.isValid());
		assertEquals(1, c.number());
	}

	@Test
	public void testSelection4() {
		final Configuration c = new Configuration(fm, true);
		c.setManual("A", Selection.SELECTED);
		assertTrue(c.isValid());
		assertEquals(1, c.number());
	}

	@Test
	public void testSelection5() {
		final Configuration c = new Configuration(fm, true);
		boolean exception = false;
		try {
			c.setManual("B", Selection.SELECTED);
		} catch (final SelectionNotPossibleException e) {
			exception = true;
		}
		assertTrue(exception);
	}

}
