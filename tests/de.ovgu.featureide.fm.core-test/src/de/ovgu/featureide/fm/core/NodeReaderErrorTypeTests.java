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

import java.util.Arrays;
import java.util.Collection;

import org.junit.Assert;
import org.junit.Test;
import org.prop4j.ErrorType.ErrorEnum;
import org.prop4j.NodeReader;

/**
 * TODO description
 *
 * @author Iris-Maria Banciu
 */
public class NodeReaderErrorTypeTests {

	final Collection<String> featureList = Arrays.asList("A", "B", "C");
	final String badFeatureName = "R";
	String constraint = "";

	@Test
	public void errorTypeEqualsNoneTest() {
		final NodeReader reader = new NodeReader();
		reader.stringToNode(constraint, featureList);

		Assert.assertEquals(ErrorEnum.None, reader.errorType.getError());
	}

	@Test
	public void errorTypeEqualsDefaultTest() {
		final NodeReader reader = new NodeReader();
		constraint = "()";
		reader.stringToNode(constraint, featureList);

		Assert.assertEquals(ErrorEnum.Default, reader.errorType.getError());
	}

	@Test
	public void errorTypeEqualsInvalidFeatureNameTest() {
		final NodeReader reader = new NodeReader();
		constraint = badFeatureName + " or A";
		reader.stringToNode(constraint, featureList);

		Assert.assertEquals(ErrorEnum.InvalidFeatureName, reader.errorType.getError());
	}

	@Test
	public void errorTypeEqualsInvalidExpressionLeftTest() {
		final NodeReader reader = new NodeReader();
		constraint = "A or B implies implies";
		reader.stringToNode(constraint, featureList);
		Assert.assertEquals(ErrorEnum.InvalidExpressionLeft, reader.errorType.getError());
	}

	@Test
	public void errorTypeEqualsInvalidExpressionRightTest() {
		final NodeReader reader = new NodeReader();
		constraint = "A or B or ";
		reader.stringToNode(constraint, featureList);
		Assert.assertEquals(ErrorEnum.InvalidExpressionRight, reader.errorType.getError());
	}
}
