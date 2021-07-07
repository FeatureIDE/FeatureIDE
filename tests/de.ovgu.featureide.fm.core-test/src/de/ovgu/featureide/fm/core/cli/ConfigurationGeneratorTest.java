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
package de.ovgu.featureide.fm.core.cli;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.junit.Test;

import de.ovgu.featureide.Commons;
import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.SolutionList;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.SampleTester;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.TWiseCoverageCriterion;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.csv.ConfigurationListFormat;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;

/**
 * Tests sampling algorithms.
 *
 * @author Sebastian Krieter
 */
public class ConfigurationGeneratorTest {

	private final static Path modelDirectory = Commons.getRemoteOrLocalFolder(Commons.TEST_FEATURE_MODEL_PATH).toPath();

	private final List<String> modelNames = Arrays.asList( //
			"basic", //
			"simple", //
			"car", //
			"gpl_medium_model");

	@Test
	public void AllCoverage() {
		testSize("basic", "all", 1);
		testSize("simple", "all", 2);
		testSize("car", "all", 7);
		testSize("gpl_medium_model", "all", 960);
	}

	@Test
	public void AllLimit() {
		testLimitedSize("basic", "all", 1, 0);
		testLimitedSize("basic", "all", 1, 1);
		testLimitedSize("basic", "all", 1, 2);
		testLimitedSize("simple", "all", 2, 1);
		testLimitedSize("simple", "all", 2, 2);
		testLimitedSize("simple", "all", 2, 3);
		testLimitedSize("car", "all", 7, 0);
		testLimitedSize("car", "all", 7, 1);
		testLimitedSize("car", "all", 7, 5);
		testLimitedSize("car", "all", 7, 7);
		testLimitedSize("car", "all", 7, 10);
		testLimitedSize("car", "all", 7, Integer.MAX_VALUE);
		testLimitedSize("gpl_medium_model", "all", 960, 10);
		testLimitedSize("gpl_medium_model", "all", 960, 960);
		testLimitedSize("gpl_medium_model", "all", 960, Integer.MAX_VALUE);
	}

	@Test
	public void RandomLimit() {
		testLimitedSize("basic", "random", 1, 0);
		testLimitedSize("basic", "random", 1, 1);
		testLimitedSize("basic", "random", 1, 2);
		testLimitedSize("simple", "random", 2, 1);
		testLimitedSize("simple", "random", 2, 2);
		testLimitedSize("simple", "random", 2, 3);
		testLimitedSize("car", "random", 7, 0);
		testLimitedSize("car", "random", 7, 1);
		testLimitedSize("car", "random", 7, 5);
		testLimitedSize("car", "random", 7, 7);
		testLimitedSize("car", "random", 7, 10);
		testLimitedSize("car", "random", 7, Integer.MAX_VALUE);
		testLimitedSize("gpl_medium_model", "random", 960, 10);
		testLimitedSize("gpl_medium_model", "random", 960, 960);
		testLimitedSize("gpl_medium_model", "random", 960, Integer.MAX_VALUE);
		testLimitedSize("apl_model", "random", 100, 100);
	}

	@Test
	public void ChvatalLimit() {
		testTWiseLimitedSize("gpl_medium_model", "chvatal", 1, 5);
		testTWiseLimitedSize("gpl_medium_model", "chvatal", 2, 5);
		testTWiseLimitedSize("gpl_medium_model", "chvatal", 3, 5);
	}

	@Test
	public void ICPLLimit() {
		testTWiseLimitedSize("gpl_medium_model", "icpl", 1, 5);
		testTWiseLimitedSize("gpl_medium_model", "icpl", 2, 5);
		testTWiseLimitedSize("gpl_medium_model", "icpl", 3, 5);
	}

	@Test
	public void InclingLimit() {
		testTWiseLimitedSize("gpl_medium_model", "incling", 1, 5);
		testTWiseLimitedSize("gpl_medium_model", "incling", 2, 5);
		testTWiseLimitedSize("gpl_medium_model", "incling", 3, 5);
	}

	@Test
	public void YASALimit() {
		testTWiseLimitedSize("gpl_medium_model", "yasa", 1, 5);
		testTWiseLimitedSize("gpl_medium_model", "yasa", 2, 5);
		testTWiseLimitedSize("gpl_medium_model", "yasa", 3, 5);
	}

	@Test
	public void YASAOneWiseCoverage() {
		testCoverageAndDeterminism("yasa", 1, modelNames);
	}

	@Test
	public void YASATwoWiseCoverage() {
		testCoverageAndDeterminism("yasa", 2, modelNames);
	}

	@Test
	public void YASAThreeWiseCoverage() {
		testCoverageAndDeterminism("yasa", 3, modelNames);
	}

	@Test
	public void InclingTwoWiseCoverage() {
		testCoverageAndDeterminism("incling", 2, modelNames);
	}

//	@Test
//	public void ICPLOneWiseCoverage() {
//		testCoverage("icpl", 1, modelNames);
//	}

	@Test
	public void ICPLTwoWiseCoverage() {
		testCoverage("icpl", 2, modelNames);
	}

	@Test
	public void ICPLThreeWiseCoverage() {
		testCoverage("icpl", 3, modelNames);
	}

//	@Test
//	public void ChvatalOneWiseCoverage() {
//		testCoverage("chvatal", 1, modelNames);
//	}

	@Test
	public void ChvatalTwoWiseCoverage() {
		testCoverage("chvatal", 2, modelNames);
	}

	@Test
	public void ChvatalThreeWiseCoverage() {
		testCoverage("chvatal", 3, modelNames);
	}

	private void testCoverage(final String algorithmName, final int t, final List<String> modelNameList) {
		for (final String modelName : modelNameList) {
			final Path modelFile = modelDirectory.resolve(modelName + ".xml");
			final SampleTester tester = sample(modelFile, algorithmName, t, null);
			assertFalse("Invalid solutions for " + modelName, tester.hasInvalidSolutions());
			assertEquals("Wrong coverage for " + modelName, 1.0, tester.getCoverage(new TWiseCoverageCriterion(tester.getCnf(), t)), 0.0);
		}
	}

	private void testCoverageAndDeterminism(final String algorithmName, final int t, final List<String> modelNameList) {
		for (final String modelName : modelNameList) {
			final Path modelFile = modelDirectory.resolve(modelName + ".xml");
			final SampleTester tester = sample(modelFile, algorithmName, t, null);
			assertFalse("Invalid solutions for " + modelName, tester.hasInvalidSolutions());
			assertEquals("Wrong coverage for " + modelName, 1.0, tester.getCoverage(new TWiseCoverageCriterion(tester.getCnf(), t)), 0.0);
			final SampleTester tester2 = sample(modelFile, algorithmName, t, null);
			assertEquals("Wrong size for " + modelName, tester.getSize(), tester2.getSize());
		}
	}

	private static void testSize(String modelName, String algorithm, int numberOfConfigurations) {
		final Path modelFile = modelDirectory.resolve(modelName + ".xml");
		final SampleTester tester = sample(modelFile, algorithm, null, null);
		assertFalse("Invalid solutions for " + modelName, tester.hasInvalidSolutions());
		assertEquals("Wrong number of configurations for " + modelName, numberOfConfigurations, tester.getSize());
	}

	private static void testLimitedSize(String modelName, String algorithm, int numberOfConfigurations, int limit) {
		final Path modelFile = modelDirectory.resolve(modelName + ".xml");
		final SampleTester tester = sample(modelFile, algorithm, null, limit);
		assertFalse("Invalid solutions for " + modelName, tester.hasInvalidSolutions());
		assertTrue("Number of configurations larger than limit for " + modelName, limit >= tester.getSize());
	}

	private static void testTWiseLimitedSize(String modelName, String algorithm, int t, int limit) {
		final Path modelFile = modelDirectory.resolve(modelName + ".xml");
		final SampleTester tester = sample(modelFile, algorithm, null, limit);
		assertFalse("Invalid solutions for " + modelName, tester.hasInvalidSolutions());
		assertTrue("Number of configurations larger than limit for " + modelName, limit >= tester.getSize());
	}

	private static SampleTester sample(final Path modelFile, String algorithm, Integer t, Integer limit) {
		try {
			final Path inFile = Files.createTempFile("input", ".xml");
			Files.write(inFile, Files.readAllBytes(modelFile));

			final Path outFile = Files.createTempFile("output", "");

			final ArrayList<String> args = new ArrayList<>();
			args.add("-a");
			args.add(algorithm);
			args.add("-o");
			args.add(outFile.toString());
			args.add("-fm");
			args.add(inFile.toString());

			if (t != null) {
				args.add("-t");
				args.add(Integer.toString(t));
			}
			if (limit != null) {
				args.add("-l");
				args.add(Integer.toString(limit));
			}
			new ConfigurationGenerator().run(args);

			final SolutionList sample = new SolutionList();
			FileHandler.load(outFile, sample, new ConfigurationListFormat());

			final FileHandler<IFeatureModel> fileHandler = FeatureModelManager.getFileHandler(modelFile);
			if (fileHandler.getLastProblems().containsError()) {
				fail(fileHandler.getLastProblems().getErrors().get(0).error.getMessage());
			}
			final CNF cnf = new FeatureModelFormula(fileHandler.getObject()).getCNF();

			final SampleTester tester = new SampleTester(cnf);
			tester.setSample(sample.getSolutions());
			return tester;
		} catch (final IOException e) {
			e.printStackTrace();
			fail(e.getMessage());
			return null;
		}
	}
}
