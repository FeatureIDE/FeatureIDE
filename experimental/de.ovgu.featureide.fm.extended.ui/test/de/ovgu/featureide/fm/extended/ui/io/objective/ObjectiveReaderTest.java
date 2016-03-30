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
package de.ovgu.featureide.fm.extended.ui.io.objective;

import static org.junit.Assert.assertEquals;
import de.ovgu.featureide.fm.extended.ui.io.attribute.Attributes;
import de.ovgu.featureide.fm.extended.ui.io.constraint.ReferenceType;
import de.ovgu.featureide.fm.extended.ui.io.constraint.WeightedTerm;

import java.util.HashSet;

import org.junit.Before;
import org.junit.Test;

public class ObjectiveReaderTest {

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
		ObjectiveReaderResult r = ObjectiveReader.readString(features,
				attributes, "3 Phone.foo;");

		assertEquals(0, r.getProblems().size());
		assertEquals(1, r.getObjective().size());
		WeightedTerm term = r.getObjective().get(0);
		assertEquals(3, term.getWeight().intValue());
		assertEquals(true, term.isPositive());
		assertEquals("Phone", term.getReference().getFeatureName());
		assertEquals(ReferenceType.ATTRIBUTE, term.getReference().getType());
		assertEquals("foo", term.getReference().getAttributeName());
	}
	
	@Test
	public void testReader2() {
		ObjectiveReaderResult r = ObjectiveReader.readString(features,
				attributes, "+1 ~Scr33n.foo;");

		assertEquals(0, r.getProblems().size());
		assertEquals(1, r.getObjective().size());
		WeightedTerm term = r.getObjective().get(0);
		assertEquals(1, term.getWeight().intValue());
		assertEquals(false, term.isPositive());
		assertEquals("Scr33n", term.getReference().getFeatureName());
		assertEquals(ReferenceType.ATTRIBUTE, term.getReference().getType());
		assertEquals("foo", term.getReference().getAttributeName());
	}

	@Test
	public void testReader3() {
		ObjectiveReaderResult r = ObjectiveReader.readString(features,
				attributes, "-42 ~Games  ;");

		assertEquals(0, r.getProblems().size());
		assertEquals(1, r.getObjective().size());
		WeightedTerm term = r.getObjective().get(0);
		assertEquals(-42, term.getWeight().intValue());
		assertEquals(false, term.isPositive());
		assertEquals("Games", term.getReference().getFeatureName());
		assertEquals(ReferenceType.FEATURE, term.getReference().getType());
		assertEquals(null, term.getReference().getAttributeName());
	}

	@Test
	public void testReader4() {
		ObjectiveReaderResult r = ObjectiveReader.readString(features,
				attributes, " -42 Games -1 ~Calls.bar;");
		
		assertEquals(0, r.getProblems().size());
		assertEquals(2, r.getObjective().size());
		
		WeightedTerm term1;
		WeightedTerm term2;
		if (r.getObjective().get(0).getReference().getFeatureName() == "Games") {
			term1 = r.getObjective().get(0);
			term2 = r.getObjective().get(1);
		} else {
			term1 = r.getObjective().get(1);
			term2 = r.getObjective().get(0);
		}
		
		assertEquals(-42, term1.getWeight().intValue());
		assertEquals(true, term1.isPositive());
		assertEquals("Games", term1.getReference().getFeatureName());
		assertEquals(ReferenceType.FEATURE, term1.getReference().getType());
		assertEquals(null, term1.getReference().getAttributeName());

		assertEquals(-1, term2.getWeight().intValue());
		assertEquals(false, term2.isPositive());
		assertEquals("Calls", term2.getReference().getFeatureName());
		assertEquals(ReferenceType.ATTRIBUTE, term2.getReference().getType());
		assertEquals("bar", term2.getReference().getAttributeName());
	}

	@Test
	public void testReader5() {
		ObjectiveReaderResult r = ObjectiveReader.readString(features,
				attributes, "+ ~Phone - Calls.bar ;");

		assertEquals(0, r.getProblems().size());
		assertEquals(2, r.getObjective().size());
		
		WeightedTerm term1;
		WeightedTerm term2;
		if (r.getObjective().get(0).getReference().getFeatureName() == "Phone") {
			term1 = r.getObjective().get(0);
			term2 = r.getObjective().get(1);
		} else {
			term1 = r.getObjective().get(1);
			term2 = r.getObjective().get(0);
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
		ObjectiveReaderResult r = ObjectiveReader.readString(features,
				attributes, "123459 ~Phone#bar -123456~Games.foo;");

		assertEquals(0, r.getProblems().size());
		assertEquals(2, r.getObjective().size());
		
		WeightedTerm term1;
		WeightedTerm term2;
		if (r.getObjective().get(0).getReference().getFeatureName() == "Phone") {
			term1 = r.getObjective().get(0);
			term2 = r.getObjective().get(1);
		} else {
			term1 = r.getObjective().get(1);
			term2 = r.getObjective().get(0);
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
		ObjectiveReaderResult r = ObjectiveReader.readString(features,
				attributes, "++1 Phone;");

//		assertEquals(1, r.getProblems().size());
		assertEquals(null, r.getObjective());
	}

	@Test
	public void testReaderProblem2() {
		ObjectiveReaderResult r = ObjectiveReader.readString(features,
				attributes, "+1 ~Phoe;");

		assertEquals(1, r.getProblems().size());
		assertEquals(null, r.getObjective());
	}
	
	@Test
	public void testReaderProblem3() {
		ObjectiveReaderResult r = ObjectiveReader.readString(features,
				attributes, "+ ~Phone.fooo;");

		assertEquals(1, r.getProblems().size());
		assertEquals(null, r.getObjective());
	}

	@Test
	public void testReaderProblem4() {
		ObjectiveReaderResult r = ObjectiveReader.readString(features,
				attributes, "+ ~Phone.bar == 1;");

		assertEquals(1, r.getProblems().size());
		assertEquals(null, r.getObjective());
	}

	@Test
	public void testReaderProblem6() {
		ObjectiveReaderResult r = ObjectiveReader.readString(features,
				attributes, "+ = ~Phone.bar == 1;");

		assertEquals(1, r.getProblems().size());
		assertEquals(null, r.getObjective());
	}
	
	@Test
	public void testReaderProblem7() {
		ObjectiveReaderResult r = ObjectiveReader.readString(features,
				attributes, "+1 +3 Phone;");

		assertEquals(1, r.getProblems().size());
		assertEquals(null, r.getObjective());
	}
	
	@Test
	public void testReaderProblem8() {
		ObjectiveReaderResult r = ObjectiveReader.readString(features,
				attributes, "Scr33n # ;");

		assertEquals(1, r.getProblems().size());
		assertEquals(null, r.getObjective());
	}
	
	@Test
	public void testReaderProblem9() {
		ObjectiveReaderResult r = ObjectiveReader.readString(features,
				attributes, "Scr33n <= 3");

		assertEquals(1, r.getProblems().size());
		assertEquals(null, r.getObjective());
	}
}
