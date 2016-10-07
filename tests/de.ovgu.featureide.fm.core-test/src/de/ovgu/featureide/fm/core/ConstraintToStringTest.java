/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;

public class ConstraintToStringTest {
	
	@Test
	public void testIffQuoteToString() {
		IFeatureModel fm = FMFactoryManager.getFactory().createFeatureModel();
		IConstraint c = FMFactoryManager.getFactory().createConstraint(fm, new Equals(new Literal("A"), new Literal("implies")));
		final String s = Constraints.autoQuote(c);
		
		Assert.assertEquals("A iff \"implies\"", s);
	}
	
	@Test
	public void testStandardToString() {
		IFeatureModel fm = FMFactoryManager.getFactory().createFeatureModel();
		IConstraint c = FMFactoryManager.getFactory().createConstraint(fm, new Implies(new Literal("A"), new Literal("implies")));
		Assert.assertEquals("A implies implies", c.getNode().toString(NodeWriter.textualSymbols));
	}
	
	@Test
	public void testAutoQuoteToString() {
		IFeatureModel fm = FMFactoryManager.getFactory().createFeatureModel();
		IConstraint c = FMFactoryManager.getFactory().createConstraint(fm, new Implies(new Literal("A"), new Literal("implies")));
		Assert.assertEquals("A implies \"implies\"", Constraints.autoQuote(c));
	}
	
	@Test
	public void testAutoQuoteToString2() {
		IFeatureModel fm = FMFactoryManager.getFactory().createFeatureModel();
		IConstraint c = FMFactoryManager.getFactory().createConstraint(fm, new Implies(new Literal("A B"), new Literal("implies")));
		Assert.assertEquals("\"A B\" implies \"implies\"", Constraints.autoQuote(c));
	}
	
	@Test
	public void testAutoQuoteToString3() {
		IFeatureModel fm = FMFactoryManager.getFactory().createFeatureModel();
		IConstraint c = FMFactoryManager.getFactory().createConstraint(fm, new Implies(new Literal("    A B    "), new Literal("implies")));
		Assert.assertEquals("\"    A B    \" implies \"implies\"", Constraints.autoQuote(c));
	}
	
	@Test
	public void testAutoQuoteToString4() {
		IFeatureModel fm = FMFactoryManager.getFactory().createFeatureModel();
		IConstraint c = FMFactoryManager.getFactory().createConstraint(fm, new Implies(new Literal("    A B    "), new Literal(" a b ")));
		Assert.assertEquals("\"    A B    \" implies \" a b \"", Constraints.autoQuote(c));
	}
	
	@Test
	public void testAutoQuoteToString5() {
		IConstraint c = FMFactoryManager.getFactory().createConstraint(FMFactoryManager.getFactory().createFeatureModel(), new Implies(new Literal("a"), new Literal("b")));
		Assert.assertEquals("a implies b", Constraints.autoQuote(c));
	}
	
	@Test
	public void testSplit1() {
		final String constraint = "- (A  =>  \" A\"  |  - - (\"A \"  &  and  =>  \" and\"  &  \" and\"  |  \" and \"  &  \" and\"  &  - \" and\"))";
		final String exptected = "not ( A implies \" A\" or not not ( \"A \" and \"and\" implies \" and\" and \" and\" or \" and \" and \" and\" and not \" and\" ))";
		Assert.assertEquals(exptected, Constraints.autoQuote(constraint));
	}
	
	@Test
	public void testSplit2() {
		final String constraint = "- \"Permission Control\"  &  (\"Person Prio\"  |  Service)";
		final String exptected = "not \"Permission Control\" and ( \"Person Prio\" or Service )";
		Assert.assertEquals(exptected, Constraints.autoQuote(constraint));
	}
	
	
}
