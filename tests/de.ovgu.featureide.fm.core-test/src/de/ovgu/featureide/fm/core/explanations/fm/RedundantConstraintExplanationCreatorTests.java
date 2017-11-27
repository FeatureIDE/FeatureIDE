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
package de.ovgu.featureide.fm.core.explanations.fm;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import de.ovgu.featureide.Commons;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Tests for {@link RedundantConstraintExplanationCreator}.
 *
 * @author Timo G&uuml;nther
 */
public class RedundantConstraintExplanationCreatorTests
		extends FeatureModelExplanationCreatorTests<IConstraint, RedundantConstraintExplanation, RedundantConstraintExplanationCreator> {

	@Test
	public void testCar() {
		final RedundantConstraintExplanationCreator c = getInstance();
		final IFeatureModel fm = Commons.loadTestFeatureModelFromFile("car.xml");
		c.setFeatureModel(fm);
		c.setSubject(fm.getConstraints().get(0));
		assertTrue(isValid(c.getExplanation()));
		c.setSubject(fm.getConstraints().get(1));
		assertTrue(isValid(c.getExplanation()));
		assertTrue(isValid(c.getExplanation()));
		c.setSubject(fm.getConstraints().get(3));
		assertTrue(isValid(c.getExplanation()));
	}

	@Override
	protected RedundantConstraintExplanationCreator getInstance() {
		return FeatureModelExplanationCreatorFactory.getDefault().getRedundantConstraintExplanationCreator();
	}
}
