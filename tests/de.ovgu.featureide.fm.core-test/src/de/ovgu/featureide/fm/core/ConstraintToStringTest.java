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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core;

import org.junit.Assert;
import org.junit.Test;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.NodeReader;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;

public class ConstraintToStringTest {

	private IFeatureModelFactory getFMFactory() {
		return FMFactoryManager.getDefaultFactory();
	}

	@Test
	public void testIffQuoteToString() {
		final IFeatureModelFactory factory = getFMFactory();
		final IFeatureModel fm = factory.createFeatureModel();
		final IConstraint c = factory.createConstraint(fm, new Equals(new Literal("A"), new Literal("implies")));
		final String s = c.getNode().toString(NodeWriter.textualSymbols);

		Assert.assertEquals("A iff \"implies\"", s);
	}

	@Test
	public void testStandardToString() {
		final IFeatureModelFactory factory = getFMFactory();
		final IFeatureModel fm = factory.createFeatureModel();
		final IConstraint c = factory.createConstraint(fm, new Implies(new Literal("A"), new Literal("implies")));
		final NodeWriter nodeWriter = new NodeWriter(c.getNode());
		nodeWriter.setSymbols(NodeWriter.textualSymbols);
		nodeWriter.setEnforceBrackets(false);
		nodeWriter.setEnquoteWhitespace(false);
		Assert.assertEquals("A implies implies", nodeWriter.nodeToString());
	}

	@Test
	public void testAutoQuoteToString() {
		final IFeatureModelFactory factory = getFMFactory();
		final IFeatureModel fm = factory.createFeatureModel();
		final IConstraint c = factory.createConstraint(fm, new Implies(new Literal("A"), new Literal("implies")));
		Assert.assertEquals("A implies \"implies\"", c.getNode().toString(NodeWriter.textualSymbols));
	}

	@Test
	public void testAutoQuoteToString2() {
		final IFeatureModelFactory factory = getFMFactory();
		final IFeatureModel fm = factory.createFeatureModel();
		final IConstraint c = factory.createConstraint(fm, new Implies(new Literal("A B"), new Literal("implies")));
		Assert.assertEquals("\"A B\" implies \"implies\"", c.getNode().toString(NodeWriter.textualSymbols));
	}

	@Test
	public void testAutoQuoteToString3() {
		final IFeatureModelFactory factory = getFMFactory();
		final IFeatureModel fm = factory.createFeatureModel();
		final IConstraint c = factory.createConstraint(fm, new Implies(new Literal("    A B    "), new Literal("implies")));
		Assert.assertEquals("\"    A B    \" implies \"implies\"", c.getNode().toString(NodeWriter.textualSymbols));
	}

	@Test
	public void testAutoQuoteToString4() {
		final IFeatureModelFactory factory = getFMFactory();
		final IFeatureModel fm = factory.createFeatureModel();
		final IConstraint c = factory.createConstraint(fm, new Implies(new Literal("    A B    "), new Literal(" a b ")));
		Assert.assertEquals("\"    A B    \" implies \" a b \"", c.getNode().toString(NodeWriter.textualSymbols));
	}

	@Test
	public void testAutoQuoteToString5() {
		final IFeatureModelFactory factory = getFMFactory();
		final IFeatureModel fm = factory.createFeatureModel();
		final IConstraint c = factory.createConstraint(fm, new Implies(new Literal("a"), new Literal("b")));
		Assert.assertEquals("a implies b", c.getNode().toString(NodeWriter.textualSymbols));
	}

	@Test
	public void testSplit1() {
		final String constraint = "- (A  =>  \" A\"  |  - - (\"A \"  &  and  =>  \" and\"  &  \" and\"  |  \" and \"  &  \" and\"  &  - \" and\"))";
		final String exptected =
			"not (A implies \" A\" or not (not (\"A \" and \"and\" implies \" and\" and \" and\" or \" and \" and \" and\" and not \" and\")))";
		final NodeReader nodeReader = new NodeReader();
		nodeReader.activateShortSymbols();
		final String string = nodeReader.stringToNode(constraint).toString(NodeWriter.textualSymbols);
		Assert.assertEquals(exptected, string);
	}

	@Test
	public void testSplit2() {
		final String constraint = "- \"Permission Control\"  &  (\"Person Prio\"  |  Service)";
		final String exptected = "not \"Permission Control\" and (\"Person Prio\" or Service)";
		final NodeReader nodeReader = new NodeReader();
		nodeReader.activateShortSymbols();
		Assert.assertEquals(exptected, nodeReader.stringToNode(constraint).toString(NodeWriter.textualSymbols));
	}

}
