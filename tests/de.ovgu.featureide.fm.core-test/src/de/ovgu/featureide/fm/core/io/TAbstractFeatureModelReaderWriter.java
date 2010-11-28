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
package de.ovgu.featureide.fm.core.io;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.FileNotFoundException;

import org.junit.Before;
import org.junit.Test;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.Comparison;
import de.ovgu.featureide.fm.core.editing.ModelComparator;
import de.ovgu.featureide.fm.core.io.guidsl.GuidslReader;

/**
 * Basic test super-class for IFeatureModelReader/IFeatureModelWriter
 * implementations tests will write feature-models into a string and read it
 * back to check if the result is as expected
 * 
 * To add additional readers/writers extend this class and override abstract
 * methods
 * 
 * @author Fabian Benduhn
 */
public abstract class TAbstractFeatureModelReaderWriter {

	// featuremodels are created by using GuidslWriter, so for each test case
	// there should be an corresponding test case for the
	// GuidslReader which tests the resulting FeatureModel directly
	// TODO: add Strings for additional test cases
	protected static String AND_GROUP_ALL_OPTIONAL = "Root : [Base] :: _Root ; Base : [A] [B] [C] :: _Base ;";
	protected static String AND_GROUP_A_MANDATORY = "Root : [Base] :: _Root ; Base : A [B] [C] :: _Base ;";
	protected static String OR_GROUP = "Root : Base* :: _Root ;Base : A	| B	| C ;";
	protected static String ALTERNATIVE_GROUP = "Root : Base ;Base : A| B	| C ;";

	protected static String SIMPLE_MANDATORY = "Root : A :: _Root ;";
	protected static String SINGLE_OR = "Root_ : Root+ :: _Root ;Root : A ;";
	protected static String AND_ALTERNATIVE = "Root : A B :: _Root ;B : C| D ;";
	protected static String AND_OR = "Root : A B+ :: _Root ;B : C	| D ;";
	protected static String CHILD_AND_MANDATORY = "Root : A B :: _Root ;B : C D :: _B ;";
	protected static String CHILD_AND_OPTIONAL = "Root : A B :: _Root ;B : C [D] :: _B ;";

	protected static String HIDDEN_FEATURE = "Root : [B] [A] :: _Root ;%%not (B or A) ;";

	protected static String CONSTRAINT_A_IMPLIES_B = "Root : A B :: _Root ;%%A implies B ;";
	protected static String CONSTRAINT_A_AND_B = "Root : A B :: _Root ;%%A and B ;";
	protected static String CONSTRAINT_A_OR_B = "Root : A B :: _Root ;%%A or B ;";
	protected static String CONSTRAINT_A_IFF_B = "Root : A B :: _Root ;%%A iff B ;";
	protected static String CONSTRAINT_NOT_A = "Root : A B :: _Root ;%%not A ;";
	protected static String MULTIPLE_CONSTRAINTS = "Root : [A] [B] :: _Root ;%%A and B ;B or A ;A implies B ;";
	protected static String CONSTRAINT_PARANTHESIS = "Root : [B] [A] :: _Root ;%%not (B or A) ;";
	protected static String sep = System.getProperty("file.separator");

	protected static File APL_MODEL_FILE = new File("src" + sep
			+ "testFeatureModels" + sep + "APL-MODEL.m");
	IFeatureModelWriter writer;
	IFeatureModelReader reader;
	FeatureModel fm;

	@Before
	public void setUpEachTest() {
		if (fm == null)
			fm = new FeatureModel();
		else
			fm.reset();
		writer = getWriter(fm);
		reader = getReader(fm);
	}

	@Test
	public void testAlternativeGroup() {
		assertTrue(testFromString(ALTERNATIVE_GROUP));
	}

	@Test
	public void testOrGroup() {
		assertTrue(testFromString(OR_GROUP));
	}

	@Test
	public void testAndGroupAMandatory() {
		assertTrue(testFromString(AND_GROUP_A_MANDATORY));
	}

	@Test
	public void testAndGroupAllOptional() {
		assertTrue(testFromString(AND_GROUP_ALL_OPTIONAL));
	}

	@Test
	public void testSimpleMandatory() {
		assertTrue(testFromString(SIMPLE_MANDATORY));
	}

	@Test
	public void testSingleOr() {
		assertTrue(testFromString(SINGLE_OR));
	}

	@Test
	public void testAndAlternative() {
		assertTrue(testFromString(AND_ALTERNATIVE));
	}

	@Test
	public void testAndOr() {
		assertTrue(testFromString(AND_OR));
	}

	@Test
	public void testAndAndMandatory() {
		assertTrue(testFromString(CHILD_AND_MANDATORY));
	}

	@Test
	public void testAndAndOptional() {
		assertTrue(testFromString(CHILD_AND_OPTIONAL));
	}

	@Test
	public void testConstraintAImpliesB() {
		assertTrue(testFromString(CONSTRAINT_A_IMPLIES_B));
	}

	@Test
	public void testConstraintAAndB() {
		assertTrue(testFromString(CONSTRAINT_A_AND_B));
	}

	@Test
	public void testConstraintAOrB() {
		assertTrue(testFromString(CONSTRAINT_A_OR_B));
	}

	@Test
	public void testConstraintAIffB() {
		assertTrue(testFromString(CONSTRAINT_A_IFF_B));
	}

	@Test
	public void testConstraintNotA() {
		assertTrue(testFromString(CONSTRAINT_NOT_A));
	}

	@Test
	public void testMultipleConstraints() {
		assertTrue(testFromString(MULTIPLE_CONSTRAINTS));
	}

	@Test
	public void testConstraintParanthesis() {
		assertTrue(testFromString(CONSTRAINT_PARANTHESIS));
	}

	@Test
	public void testAplModel() throws FileNotFoundException,
			UnsupportedModelException {

		assertTrue(testFromFile(APL_MODEL_FILE));
	}

	/**
	 * @param guidslReader
	 *            *
	 * */
	private boolean testFromString(String s) {
		FeatureModel fmOld = fm;
		GuidslReader guidslReader = new GuidslReader(fm);
		try {
			guidslReader.readFromString(s);

			writeAndReadModel();
		} catch (UnsupportedModelException e) {
			assertFalse(e.getMessage(), true);
		}
		return compareModels(fmOld, fm);
	}

	/**
	 * @param guidslReader
	 *            *
	 * @throws FileNotFoundException
	 * */
	private boolean testFromFile(File file) throws FileNotFoundException {
		FeatureModel fmOld = fm;
		GuidslReader guidslReader = new GuidslReader(fm);
		try {
			guidslReader.readFromFile(file);

			writeAndReadModel();
		} catch (UnsupportedModelException e) {
			assertFalse(e.getMessage(), true);
		}
		return compareModels(fmOld, fm);
	}

	/**
	 * TODO: Replace by a check for direct equality, i.e oldfm.equals(newfm)
	 * 
	 */
	private boolean compareModels(FeatureModel oldfm, FeatureModel newfm) {
		ModelComparator mc = new ModelComparator(10000);
		return (mc.compare(oldfm, newfm).equals(Comparison.REFACTORING));
	}

	public void writeAndReadModel() throws UnsupportedModelException {

		String s = writer.writeToString();

		reader.readFromString(s);

	}

	protected abstract IFeatureModelWriter getWriter(FeatureModel fm);

	protected abstract IFeatureModelReader getReader(FeatureModel fm);

}
