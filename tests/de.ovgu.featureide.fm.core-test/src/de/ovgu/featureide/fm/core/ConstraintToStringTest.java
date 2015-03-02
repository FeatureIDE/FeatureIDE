/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.ArrayList;
import java.util.Collection;

import org.junit.Assert;
import org.junit.Test;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.NodeWriter;
import org.prop4j.Not;
import org.prop4j.Or;

public class ConstraintToStringTest {
	
	@Test
	public void testStandardToString() {
		FeatureModel fm = new FeatureModel();
		Constraint c = new Constraint(fm, new Implies(new Literal("A"), new Literal("implies")));
		Assert.assertEquals("A implies implies", c.getNode().toString(NodeWriter.textualSymbols));
	}
	
	@Test
	public void testAutoQuoteToString() {
		FeatureModel fm = new FeatureModel();
		Constraint c = new Constraint(fm, new Implies(new Literal("A"), new Literal("implies")));
		Assert.assertEquals("A implies \"implies\"", Constraints.autoQuote(c));
	}
	
	@Test
	public void testAutoQuoteToString2() {
		FeatureModel fm = new FeatureModel();
		Constraint c = new Constraint(fm, new Implies(new Literal("A B"), new Literal("implies")));
		Assert.assertEquals("\"A B\" implies \"implies\"", Constraints.autoQuote(c));
	}
	
	@Test
	public void testAutoQuoteToString3() {
		FeatureModel fm = new FeatureModel();
		Constraint c = new Constraint(fm, new Implies(new Literal("    A B    "), new Literal("implies")));
		Assert.assertEquals("\"    A B    \" implies \"implies\"", Constraints.autoQuote(c));
	}
	
	@Test
	public void testAutoQuoteToString4() {
		FeatureModel fm = new FeatureModel();
		Constraint c = new Constraint(fm, new Implies(new Literal("    A B    "), new Literal(" a b ")));
		Assert.assertEquals("\"    A B    \" implies \" a b \"", Constraints.autoQuote(c));
	}
	
	@Test
	public void testAutoQuoteToString5() {
		Constraint c = new Constraint(new FeatureModel(), new Implies(new Literal("a"), new Literal("b")));
		Assert.assertEquals("a implies b", Constraints.autoQuote(c));
	}
	

}
