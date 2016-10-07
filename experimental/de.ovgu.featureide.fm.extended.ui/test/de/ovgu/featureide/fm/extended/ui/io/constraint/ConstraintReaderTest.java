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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.extended.ui.io.constraint;

import static org.junit.Assert.assertEquals;
import de.ovgu.featureide.fm.extended.ui.io.attribute.Attributes;

import java.util.HashSet;

import org.junit.Before;
import org.junit.Test;

public class ConstraintReaderTest {

	HashSet<String> features;
	Attributes attributes;

	@Before
	public void setUp() {
		features = new HashSet<String>();
		features.add("Phone");
		features.add("Calls");
		features.add("Scr33n");
		features.add("Games");
		attributes = new Attributes();
		attributes.setAttribute("Phone", "foo", 3);
		attributes.setAttribute("Phone", "bar", 2);
		attributes.setAttribute("Calls", "foo", 2);
		attributes.setAttribute("Calls", "bar", -2);
		attributes.setAttribute("Scr33n", "foo", 5);
		attributes.setAttribute("Games", "foo", 10);
	}

	@Test
	public void testReader1() {
		ConstraintReaderResult r = ConstraintReader.readString(features,
				attributes, "3 Phone.foo = 3;");

		assertEquals(0, r.getProblems().size());
		assertEquals(1, r.getConstraints().size());
		Equation eq = r.getConstraints().get(0);
		assertEquals(RelationOperator.EQUAL, eq.getOperator());
		assertEquals(3, eq.getDegree());
		assertEquals(1, eq.getWeightedTerms().size());
		WeightedTerm term = eq.getWeightedTerms().get(0);
		assertEquals(3, term.getWeight().intValue());
		assertEquals(true, term.isPositive());
		assertEquals("Phone", term.getReference().getFeatureName());
		assertEquals(ReferenceType.ATTRIBUTE, term.getReference().getType());
		assertEquals("foo", term.getReference().getAttributeName());
	}

	@Test
	public void testReader2() {
		ConstraintReaderResult r = ConstraintReader.readString(features,
				attributes, "+1 ~Scr33n.foo >= 2;");

		assertEquals(0, r.getProblems().size());
		assertEquals(1, r.getConstraints().size());
		Equation eq = r.getConstraints().get(0);
		assertEquals(RelationOperator.GREATER_EQUAL, eq.getOperator());
		assertEquals(2, eq.getDegree());
		assertEquals(1, eq.getWeightedTerms().size());
		WeightedTerm term = eq.getWeightedTerms().get(0);
		assertEquals(1, term.getWeight().intValue());
		assertEquals(false, term.isPositive());
		assertEquals("Scr33n", term.getReference().getFeatureName());
		assertEquals(ReferenceType.ATTRIBUTE, term.getReference().getType());
		assertEquals("foo", term.getReference().getAttributeName());
	}

	@Test
	public void testReader3() {
		ConstraintReaderResult r = ConstraintReader.readString(features,
				attributes, " -42 ~Games <=   -5 ;");

		assertEquals(0, r.getProblems().size());
		assertEquals(1, r.getConstraints().size());
		Equation eq = r.getConstraints().get(0);
		assertEquals(RelationOperator.LESSER_EQUAL, eq.getOperator());
		assertEquals(-5, eq.getDegree());
		assertEquals(1, eq.getWeightedTerms().size());
		WeightedTerm term = eq.getWeightedTerms().get(0);
		assertEquals(-42, term.getWeight().intValue());
		assertEquals(false, term.isPositive());
		assertEquals("Games", term.getReference().getFeatureName());
		assertEquals(ReferenceType.FEATURE, term.getReference().getType());
		assertEquals(null, term.getReference().getAttributeName());
	}

	@Test
	public void testReader4() {
		ConstraintReaderResult r = ConstraintReader.readString(features,
				attributes, " -42 Games <= -5 ;\n 1 ~Calls.bar = 1;");

		assertEquals(0, r.getProblems().size());
		assertEquals(2, r.getConstraints().size());
		Equation eq1 = r.getConstraints().get(0);
		Equation eq2 = r.getConstraints().get(1);

		assertEquals(RelationOperator.LESSER_EQUAL, eq1.getOperator());
		assertEquals(-5, eq1.getDegree());
		assertEquals(1, eq1.getWeightedTerms().size());
		WeightedTerm term1 = eq1.getWeightedTerms().get(0);
		assertEquals(-42, term1.getWeight().intValue());
		assertEquals(true, term1.isPositive());
		assertEquals("Games", term1.getReference().getFeatureName());
		assertEquals(ReferenceType.FEATURE, term1.getReference().getType());
		assertEquals(null, term1.getReference().getAttributeName());

		assertEquals(RelationOperator.EQUAL, eq2.getOperator());
		assertEquals(1, eq2.getDegree());
		assertEquals(1, eq2.getWeightedTerms().size());
		WeightedTerm term2 = eq2.getWeightedTerms().get(0);
		assertEquals(1, term2.getWeight().intValue());
		assertEquals(false, term2.isPositive());
		assertEquals("Calls", term2.getReference().getFeatureName());
		assertEquals(ReferenceType.ATTRIBUTE, term2.getReference().getType());
		assertEquals("bar", term2.getReference().getAttributeName());
	}

	@Test
	public void testReader5() {
		ConstraintReaderResult r = ConstraintReader.readString(features,
				attributes, "+ ~Phone - Calls.bar = 1;");

		assertEquals(0, r.getProblems().size());
		assertEquals(1, r.getConstraints().size());
		Equation eq = r.getConstraints().get(0);
		assertEquals(RelationOperator.EQUAL, eq.getOperator());
		assertEquals(1, eq.getDegree());
		assertEquals(2, eq.getWeightedTerms().size());

		WeightedTerm term1;
		WeightedTerm term2;
		if (eq.getWeightedTerms().get(0).getReference().getFeatureName() == "Phone") {
			term1 = eq.getWeightedTerms().get(0);
			term2 = eq.getWeightedTerms().get(1);
		} else {
			term1 = eq.getWeightedTerms().get(1);
			term2 = eq.getWeightedTerms().get(0);
		}

		assertEquals(1, term1.getWeight().intValue());
		assertEquals(false, term1.isPositive());
		assertEquals("Phone", term1.getReference().getFeatureName());
		assertEquals(ReferenceType.FEATURE, term1.getReference().getType());
		assertEquals(null, term1.getReference().getAttributeName());

		assertEquals(-1, term2.getWeight().intValue());
		assertEquals(true, term2.isPositive());
		assertEquals("Calls", term2.getReference().getFeatureName());
		assertEquals(ReferenceType.ATTRIBUTE, term2.getReference().getType());
		assertEquals("bar", term2.getReference().getAttributeName());
	}

	@Test
	public void testReader6() {
		ConstraintReaderResult r = ConstraintReader.readString(features,
				attributes, "123459 ~Phone#bar -123456~Games.foo >= 3;");

		assertEquals(0, r.getProblems().size());
		assertEquals(1, r.getConstraints().size());
		Equation eq = r.getConstraints().get(0);
		assertEquals(RelationOperator.GREATER_EQUAL, eq.getOperator());
		assertEquals(3, eq.getDegree());
		assertEquals(2, eq.getWeightedTerms().size());

		WeightedTerm term1;
		WeightedTerm term2;
		if (eq.getWeightedTerms().get(0).getReference().getFeatureName() == "Scr33n") {
			term1 = eq.getWeightedTerms().get(0);
			term2 = eq.getWeightedTerms().get(1);
		} else {
			term1 = eq.getWeightedTerms().get(1);
			term2 = eq.getWeightedTerms().get(0);
		}

		assertEquals(123459, term1.getWeight().intValue());
		assertEquals(false, term1.isPositive());
		assertEquals("Phone", term1.getReference().getFeatureName());
		assertEquals(ReferenceType.ATTRIBUTE_SUM, term1.getReference()
				.getType());
		assertEquals("bar", term1.getReference().getAttributeName());

		assertEquals(-123456, term2.getWeight().intValue());
		assertEquals(false, term2.isPositive());
		assertEquals("Games", term2.getReference().getFeatureName());
		assertEquals(ReferenceType.ATTRIBUTE, term2.getReference().getType());
		assertEquals("foo", term2.getReference().getAttributeName());
	}

	@Test
	public void testReaderProblem1() {
		ConstraintReaderResult r = ConstraintReader.readString(features,
				attributes, "+1 Phone = 1 = ;");

		assertEquals(1, r.getProblems().size());
		assertEquals(0, r.getConstraints().size());
	}

	@Test
	public void testReaderProblem2() {
		ConstraintReaderResult r = ConstraintReader.readString(features,
				attributes, "+1 ~Phoe = 1;");

		assertEquals(1, r.getProblems().size());
		assertEquals(0, r.getConstraints().size());
	}
	
	@Test
	public void testReaderProblem3() {
		ConstraintReaderResult r = ConstraintReader.readString(features,
				attributes, "+1 ~Phoe = 1;");

		assertEquals(1, r.getProblems().size());
		assertEquals(0, r.getConstraints().size());
	}
	
	@Test
	public void testReaderProblem4() {
		ConstraintReaderResult r = ConstraintReader.readString(features,
				attributes, "+ ~Phone.fooo + = 1;");

		assertEquals(1, r.getProblems().size());
		assertEquals(0, r.getConstraints().size());
	}

	@Test
	public void testReaderProblem5() {
		ConstraintReaderResult r = ConstraintReader.readString(features,
				attributes, "+ ~Phone.bar == 1;");

		assertEquals(1, r.getProblems().size());
		assertEquals(0, r.getConstraints().size());
	}

	@Test
	public void testReaderProblem6() {
		ConstraintReaderResult r = ConstraintReader.readString(features,
				attributes, "+ = ~Phone.bar == 1;");

		assertEquals(1, r.getProblems().size());
		assertEquals(0, r.getConstraints().size());
	}
	
	@Test
	public void testReaderProblem7() {
		ConstraintReaderResult r = ConstraintReader.readString(features,
				attributes, "+1 = +3 Phone;");

		assertEquals(1, r.getProblems().size());
		assertEquals(0, r.getConstraints().size());
	}
	
	@Test
	public void testReaderProblem8() {
		ConstraintReaderResult r = ConstraintReader.readString(features,
				attributes, "Scr33n <= ;");

		assertEquals(1, r.getProblems().size());
		assertEquals(0, r.getConstraints().size());
	}
	
	@Test
	public void testReaderProblem9() {
		ConstraintReaderResult r = ConstraintReader.readString(features,
				attributes, "Scr33n <= 3");

		assertEquals(1, r.getProblems().size());
		assertEquals(0, r.getConstraints().size());
	}
}
