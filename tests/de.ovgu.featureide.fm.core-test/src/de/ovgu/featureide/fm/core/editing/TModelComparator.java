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
package de.ovgu.featureide.fm.core.editing;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.FileNotFoundException;
import java.util.HashSet;
import java.util.Set;

import org.junit.Test;
import org.prop4j.Node;
import org.prop4j.NodeReader;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.Commons;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.guidsl.GuidslFormat;

/**
 * Checks that the calculation of edit categories works properly. A couple of known refactorings, generalizations and arbitrary edits are performed and the
 * result of the ModelComperator is tested.
 *
 * @author Thomas Thuem
 * @author Fabian Benduhn
 * @author Marcus Pinnecke, 01.07.15
 */
public class TModelComparator {

	private static final long TIMEOUT = 1000;

	/**
	 * Refactoring: OR => OPTIONAL AND (where S is abstract)
	 */
	@Test
	public void testRefactoring1() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.REFACTORING, compare("S_ : S+ :: _S; S : A | B;", "S : [A] [B] :: _S; %% A or B;"));
	}

	// TODO warn the user when the feature model contains the empty product in
	// an FOP project

	/**
	 * Refactoring: ALTERNATIVE => OR and constraint
	 */
	@Test
	public void testRefactoring2() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.REFACTORING, compare("S : A | B;", "S_ : S+ :: _S; S : A | B; %% not (A and B);"));
	}

	/**
	 * Refactoring: MANDATORY => OPTIONAL and constraint
	 */
	@Test
	public void testRefactoring3() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.REFACTORING, compare("S : A B :: _S;", "S : [A] B :: _S; %% S implies A;"));
	}

	/**
	 * Refactoring: move feature upwards
	 */
	@Test
	public void testRefactoring4() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.REFACTORING, compare("S : A T :: _S; T : [B] C :: _T;", "S : A [B] T :: _S; T : C :: _T;"));
	}

	/**
	 * Refactoring: add abstract feature
	 */
	@Test
	public void testRefactoring5() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.REFACTORING, compare("S : A | B;", "S : T; T : A | B;"));
	}

	/**
	 * Refactoring: move feature
	 */
	@Test
	public void testRefactoring6() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.REFACTORING, compare("S : [T] C :: _S; T : [A] B :: _T;", "S : [T] [B] C :: _S; T : [A] :: _T; %% T iff B;"));
	}

	/**
	 * Refactoring: duplicate Constraint
	 */
	@Test
	public void testDuplicateConstraintRefactoring() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.REFACTORING, compare(
				"TankWar : Platform Tools* [explodieren] GUI [Record] [Soundeffekt] Language Tanks+ AI :: _TankWar ;\n\nPlatform : PC\n\u0009| Handy ;\n\nTools : Beschleunigung\n\u0009| einfrieren\n\u0009| Bombe\n\u0009| Energie\n\u0009| Feuerkraft\n\u0009| Mars ;\n\nGUI : Map [Image] :: _GUI ;\n\nMap : M_240\n\u0009| M_600\n\u0009| M_780 ;\n\nImage : [fuer_PC] [fuer_Handy] [IMG_tool] :: _Image ;\n\nRecord : Re_fuer_PC\n\u0009| Re_fuer_Handy ;\n\nSoundeffekt : Sound_fuer_pc\n\u0009| Sound_fuer_Handy ;\n\nLanguage : EN\n\u0009| DE ;\n\nTanks : USA_M1Abrams\n\u0009| Germany_Leopard\n\u0009| China_Type99 ;\n\nAI : Easy\n\u0009| Hard ;\n\n%%\n\nTools iff IMG_tool ;\nTools iff IMG_tool ;\n\n##\n\nAI { hidden } \nexplodieren { hidden } ",
				"TankWar : Platform Tools* [explodieren] GUI [Record] [Soundeffekt] Language Tanks+ AI :: _TankWar ;\n\nPlatform : PC\n\u0009| Handy ;\n\nTools : Beschleunigung\n\u0009| einfrieren\n\u0009| Bombe\n\u0009| Energie\n\u0009| Feuerkraft\n\u0009| Mars ;\n\nGUI : Map [Image] :: _GUI ;\n\nMap : M_240\n\u0009| M_600\n\u0009| M_780 ;\n\nImage : [fuer_PC] [fuer_Handy] [IMG_tool] :: _Image ;\n\nRecord : Re_fuer_PC\n\u0009| Re_fuer_Handy ;\n\nSoundeffekt : Sound_fuer_pc\n\u0009| Sound_fuer_Handy ;\n\nLanguage : EN\n\u0009| DE ;\n\nTanks : USA_M1Abrams\n\u0009| Germany_Leopard\n\u0009| China_Type99 ;\n\nAI : Easy\n\u0009| Hard ;\n\n%%\n\nTools iff IMG_tool ;\n\n##\n\nAI { hidden } \nexplodieren { hidden } "));

	}

	@Test
	public void testDuplicateConstraintRefactoring2() throws TimeoutException, UnsupportedModelException {
		final NodeReader reader = new NodeReader();
		final Node a = reader.stringToNode("A  and  (not A or B or C)  and D ");
		final Node b = reader.stringToNode("A  and  (not A or B or C)  and D ");
		final ModelComparator comparator = new ModelComparator(TIMEOUT);
		assertTrue(comparator.implies(a, b, new ExampleCalculator(null, 2500)));

	}

	/**
	 * Refactoring: deleting abstract feature
	 *
	 */
	@Test
	public void testDeleteAbstractFeatureRefactoring() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.REFACTORING, compare(
				"TankWar : Platform Tools* [explodieren] GUI [Record] [Soundeffekt] Language Tanks+ AI :: _TankWar ;\n\nPlatform : PC\n\u0009| Handy ;\n\nTools : Beschleunigung\n\u0009| einfrieren\n\u0009| Bombe\n\u0009| Energie\n\u0009| Feuerkraft\n\u0009| Mars ;\n\nGUI : Map [Image] :: _GUI ;\n\nMap : M_240\n\u0009| M_600\n\u0009| M_780 ;\n\nImage : [fuer_PC] [fuer_Handy] [IMG_tool] :: _Image ;\n\nRecord : Re_fuer_PC\n\u0009| Re_fuer_Handy ;\n\nSoundeffekt : Sound_fuer_pc\n\u0009| Sound_fuer_Handy ;\n\nLanguage : EN\n\u0009| DE ;\n\nTanks : USA_M1Abrams\n\u0009| Germany_Leopard\n\u0009| China_Type99 ;\n\nAI : Easy\n\u0009| Hard ;\n\n##\n\nAI { hidden } \nexplodieren { hidden } \n",
				"TankWar : Platform Tools* [explodieren] Map [Image] [Record] [Soundeffekt] Language Tanks+ AI :: _TankWar ;\n\nPlatform : PC\n\u0009| Handy ;\n\nTools : Beschleunigung\n\u0009| einfrieren\n\u0009| Bombe\n\u0009| Energie\n\u0009| Feuerkraft\n\u0009| Mars ;\n\nMap : M_240\n\u0009| M_600\n\u0009| M_780 ;\n\nImage : [fuer_PC] [fuer_Handy] [IMG_tool] :: _Image ;\n\nRecord : Re_fuer_PC\n\u0009| Re_fuer_Handy ;\n\nSoundeffekt : Sound_fuer_pc\n\u0009| Sound_fuer_Handy ;\n\nLanguage : EN\n\u0009| DE ;\n\nTanks : USA_M1Abrams\n\u0009| Germany_Leopard\n\u0009| China_Type99 ;\n\nAI : Easy\n\u0009| Hard ;\n\n##\n\nAI { hidden } \nexplodieren { hidden } \n"));
	}

	/**
	 * Refactoring: adding dead feature
	 *
	 */
	@Test
	public void testAddDeadFeatureRefactoring() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.REFACTORING, compare("S : [A] :: _S ;\n\n", "S : [A] [B] :: _S ;\n\n%%\n\nnot B ;\n\n"));
	}

	/**
	 * Generalization: ALTERNATIVE => OR
	 */
	@Test
	public void testGeneralization1() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.GENERALIZATION, compare("S : A | B;", "S_ : S+ :: _S; S : A | B;"));
	}

	/**
	 * Generalization: move OPTIONAL into OR
	 */
	@Test
	public void testGeneralization2() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.GENERALIZATION, compare("S : T+ [C] :: _S; T : A | B;", "S : T+ :: _S; T : A | B | C;"));
	}

	/**
	 * Generalization: AND => OR
	 */
	@Test
	public void testGeneralization3() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.GENERALIZATION, compare("S : [A] B :: _S;", "S_ : S+ :: _S; S : A | B;"));
	}

	/**
	 * Generalization: new feature in ALTERNATIVE
	 */
	@Test
	public void testGeneralization4() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.GENERALIZATION, compare("S : A | B;", "S : A | B | C;"));
	}

	/**
	 * Generalization: OR => OPTIONAL AND (where S is concrete)
	 */
	@Test
	public void testGeneralization5() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.GENERALIZATION, compare("//NoAbstractFeatures\nS_ : S+ :: _S; S : A | B;", "//NoAbstractFeatures\nS : [A] [B] :: _S;"));
	}

	/**
	 * Generalization: MANDATORY => OPTIONAL
	 */
	@Test
	public void testGeneralization6() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.GENERALIZATION, compare("S : A [B] :: _S;", "S : [A] [B] :: _S;"));
	}

	/**
	 * Generalization: ALTERNATIVE => OPTIONAL AND
	 */
	@Test
	public void testGeneralization7() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.GENERALIZATION, compare("S : A | B;", "S : [A] [B] :: _S;"));
	}

	/**
	 * Generalization: new optional feature in AND
	 */
	@Test
	public void testGeneralization8() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.GENERALIZATION, compare("S : [A] B :: _S;", "S : [A] B [C] :: _S;"));
	}

	/**
	 * Generalization: remove constraint
	 */
	@Test
	public void testGeneralization9() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.GENERALIZATION, compare("S : [A] [B] :: _S; %% A implies B;", "S : [A] [B] :: _S;"));
	}

	/**
	 * Arbitrary edit: new mandatory feature
	 */
	@Test
	public void testArbitraryEdit1() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.ARBITRARY, compare("S : A [B] :: _S;", "S : A [B] C :: _S;"));
	}

	/**
	 * Arbitrary edit: add and remove optional feature
	 */
	@Test
	public void testArbitraryEdit2() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.ARBITRARY, compare("S : [A] B :: _S;", "S : B [C] :: _S;"));
	}

	/**
	 * Arbitrary edit: AND => ALTERNATIVE
	 */
	@Test
	public void testArbitraryEdit3() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.ARBITRARY, compare("S : [A] B :: _S;", "S : A | B;"));
	}

	/**
	 * Arbitrary edit: add and remove constraint
	 */
	@Test
	public void testArbitraryEdit4() throws TimeoutException, UnsupportedModelException {
		assertEquals(Comparison.ARBITRARY, compare("S : [A] [B] :: _S; %% A implies B;", "S : [A] [B] :: _S; %% B implies A;"));
	}

	@Test
	public void testImpliesSameVariable() throws TimeoutException, UnsupportedModelException {
		final NodeReader reader = new NodeReader();
		final Node a = reader.stringToNode("A");
		final Node b = reader.stringToNode("A");
		final ModelComparator comparator = new ModelComparator(TIMEOUT);
		assertTrue(comparator.implies(a, b, new ExampleCalculator(null, 2500)));

	}

	@Test
	public void testImpliesSameVariable2() throws TimeoutException, UnsupportedModelException {
		final NodeReader reader = new NodeReader();
		final Node a = reader.stringToNode("A and A ");
		final Node b = reader.stringToNode("A and A ");
		final ModelComparator comparator = new ModelComparator(TIMEOUT);
		assertTrue(comparator.implies(a, b, new ExampleCalculator(null, 2500)));

	}

	private Comparison compare(String fm1, String fm2) throws UnsupportedModelException {
		final ModelComparator comperator = new ModelComparator(TIMEOUT);
		final IFeatureModel oldModel = FMFactoryManager.getDefaultFactory().createFeatureModel();
		final GuidslFormat reader = new GuidslFormat();
		reader.read(oldModel, fm1);
		final IFeatureModel newModel = FMFactoryManager.getDefaultFactory().createFeatureModel();
		reader.read(newModel, fm2);
		return comperator.compare(oldModel, newModel);
	}

	@Test
	/**
	 * Based on https://github.com/tthuem/FeatureIDE/issues/264
	 *
	 * @author Marcus Pinnecke
	 *
	 */
	public void testForFeatureIDEaddedProducts() throws FileNotFoundException, UnsupportedModelException, TimeoutException {
		final IFeatureModel fm = Commons.loadBenchmarkFeatureModelFromFile("issue_264_model_optional.xml");
		final IFeatureModel fmGen = Commons.loadBenchmarkFeatureModelFromFile("issue_264_model_alternative.xml");
		final ModelComparator comparator = new ModelComparator(1000000);
		final Comparison comparison = comparator.compare(fm, fmGen);

		assertEquals(Comparison.GENERALIZATION, comparison);

		final Set<String> addedProducts = new HashSet<String>();

		Configuration c;
		while ((c = comparator.calculateExample(true)) != null) {
			System.out.println(c);
			addedProducts.add(c.toString());
		}
		// TODO: assertEquals(12, addedProducts.size());
	}
}
