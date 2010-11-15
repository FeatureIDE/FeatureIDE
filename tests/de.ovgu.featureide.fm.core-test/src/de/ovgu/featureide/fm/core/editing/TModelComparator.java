/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.editing;

import static org.junit.Assert.assertEquals;

import org.junit.Test;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.IFeatureModelReader;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.guidsl.FeatureModelReader;

/**
 * Checks that the calculation of edit categories works properly. A couple of
 * known refactorings, generalizations and arbitrary edits are performed and
 * the result of the ModelComperator is tested.
 * 
 * @author Thomas Thuem
 * @author Fabian Benduhn
 */
public class TModelComparator {
	
	private static final long TIMEOUT = 1000;

	/**
	 * Refactoring: OR => OPTIONAL AND (where S is abstract)
	 */
	@Test
	public void testRefactoring1() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.REFACTORING, compare(
				"S_ : S+ :: _S; S : A | B;",
				"S : [A] [B] :: _S;"));
	}

	/**
	 * Refactoring: ALTERNATIVE => OR and constraint
	 */
	@Test
	public void testRefactoring2() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.REFACTORING, compare(
				"S : A | B;",
				"S_ : S+ :: _S; S : A | B; %% not (A and B);"));
	}

	/**
	 * Refactoring: MANDATORY => OPTIONAL and constraint
	 */
	@Test
	public void testRefactoring3() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.REFACTORING, compare(
				"S : A B :: _S;",
				"S : [A] B :: _S; %% S implies A;"));
	}

	/**
	 * Refactoring: move feature upwards
	 */
	@Test
	public void testRefactoring4() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.REFACTORING, compare(
				"S : A T :: _S; T : [B] C :: _T;",
				"S : A [B] T :: _S; T : C :: _T;"));
	}

	/**
	 * Refactoring: add abstract feature
	 */
	@Test
	public void testRefactoring5() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.REFACTORING, compare(
				"S : A | B;",
				"S : T; T : A | B;"));
	}

	/**
	 * Generalization: ALTERNATIVE => OR
	 */
	@Test
	public void testGeneralization1() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.GENERALIZATION, compare(
				"S : A | B;",
				"S_ : S+ :: _S; S : A | B;"));
	}

	/**
	 * Generalization: move OPTIONAL into OR
	 */
	@Test
	public void testGeneralization2() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.GENERALIZATION, compare(
				"S : T+ [C] :: _S; T : A | B;",
				"S : T+ :: _S; T : A | B | C;"));
	}

	/**
	 * Generalization: AND => OR
	 */
	@Test
	public void testGeneralization3() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.GENERALIZATION, compare(
				"S : [A] B :: _S;",
				"S_ : S+ :: _S; S : A | B;"));
	}

	/**
	 * Generalization: new feature in ALTERNATIVE
	 */
	@Test
	public void testGeneralization4() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.GENERALIZATION, compare(
				"S : A | B;",
				"S : A | B | C;"));
	}

	/**
	 * Generalization: OR => OPTIONAL AND (where S is concrete)
	 */
	@Test
	public void testGeneralization5() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.GENERALIZATION, compare(
				"//NoAbstractFeatures\nS_ : S+ :: _S; S : A | B;",
				"//NoAbstractFeatures\nS : [A] [B] :: _S;"));
	}

	/**
	 * Generalization: MANDATORY => OPTIONAL
	 */
	@Test
	public void testGeneralization6() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.GENERALIZATION, compare(
				"S : A [B] :: _S;",
				"S : [A] [B] :: _S;"));
	}

	/**
	 * Generalization: ALTERNATIVE => OPTIONAL AND
	 */
	@Test
	public void testGeneralization7() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.GENERALIZATION, compare(
				"S : A | B;",
				"S : [A] [B] :: _S;"));
	}

	/**
	 * Generalization: new optional feature in AND
	 */
	@Test
	public void testGeneralization8() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.GENERALIZATION, compare(
				"S : [A] B :: _S;",
				"S : [A] B [C] :: _S;"));
	}

	/**
	 * Generalization: remove constraint
	 */
	@Test
	public void testGeneralization9() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.GENERALIZATION, compare(
				"S : [A] [B] :: _S; %% A implies B;",
				"S : [A] [B] :: _S;"));
	}

	/**
	 * Arbitrary edit: new mandatory feature
	 */
	@Test
	public void testArbitraryEdit1() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.ARBITRARY, compare(
				"S : A [B] :: _S;",
				"S : A [B] C :: _S;"));
	}

	/**
	 * Arbitrary edit: add and remove optional feature
	 */
	@Test
	public void testArbitraryEdit2() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.ARBITRARY, compare(
				"S : [A] B :: _S;",
				"S : B [C] :: _S;"));
	}

	/**
	 * Arbitrary edit: AND => ALTERNATIVE
	 */
	@Test
	public void testArbitraryEdit3() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.ARBITRARY, compare(
				"S : [A] B :: _S;",
				"S : A | B;"));
	}

	/**
	 * Arbitrary edit: add and remove constraint
	 */
	@Test
	public void testArbitraryEdit4() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.ARBITRARY, compare(
				"S : [A] [B] :: _S; %% A implies B;",
				"S : [A] [B] :: _S; %% B implies A;"));
	}

	private Comparison compare(String fm1, String fm2) throws UnsupportedModelException {
		ModelComparator comperator = new ModelComparator(TIMEOUT);
		FeatureModel oldModel = new FeatureModel();
		IFeatureModelReader reader = new FeatureModelReader(oldModel);
		reader.readFromString(fm1);
		FeatureModel newModel = new FeatureModel();
		reader = new FeatureModelReader(newModel);
		reader.readFromString(fm2);
		return comperator.compare(oldModel, newModel);
	}

}
