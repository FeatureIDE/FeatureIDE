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
package de.ovgu.featureide.fm.core.experimental;

import de.ovgu.featureide.Commons;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.runtimetest.RuntimeTest;
import de.ovgu.runtimetest.RuntimeTest.Annotations.Constraint;
import de.ovgu.runtimetest.RuntimeTest.Annotations.WarmUp;

/**
 * This is a benchmark for analyzes at the {@link IFeatureModel}. The test cases do not analyze the validity of the analyses.
 *
 * All timeouts are set to around 4 times the measured times(with intel i5 @ 3,3 GHz) to avoid that the tests fail for slower computers.
 *
 * @author Jens Meinicke
 * @author Marcus Pinnecke
 */
public class BFeatureModelAnalyzerWithRuntimeConstraints extends RuntimeTest {

	static {
		disableThisTest = false;	// set this flag to true, if this test class should be skipped
	}

	/**
	 * Warm up the analyzer to prevent unpredictable timeout exceptions.
	 */
	@WarmUp
	public void warmup() {
		for (int i = 0; i < 10; i++) {
			analyze(10);
			analyze(20);
			analyze(21);
		}
	}

	/************************************************************
	 * Analyzes the model completely.
	 */
	private static void analyze(final int i) {
		getFM(i).getAnalyser().analyzeFeatureModel(null);
	}

	@Constraint(samples = 5, allowedPlus = 1500)
	public final void BAnalyzeFeatureModel0001() {
		analyze(1);
	}

	@Constraint(samples = 5, allowedPlus = 1500)
	public final void BAnalyzeFeatureModel0002() {
		analyze(2);
	}

	@Constraint(samples = 5, allowedPlus = 1500)
	public final void BAnalyzeFeatureModel0010() {
		analyze(10);
	}

	@Constraint(samples = 5, allowedPlus = 1500)
	public final void BAnalyzeFeatureModel0020() {
		analyze(20);
	}

	@Constraint(samples = 5, allowedPlus = 1500)
	public final void BAnalyzeFeatureModel0021() {
		analyze(21);
	}

	@Constraint(samples = 5, allowedPlus = 1500)
	public final void BAnalyzeFeatureModel0050() {
		analyze(50);
	}

	@Constraint(samples = 5, allowedPlus = 1500)
	public final void BAnalyzeFeatureModel0100() {
		analyze(100);
	}

	@Constraint(samples = 5, allowedPlus = 3200)
	public final void BAnalyzeFeatureModel0200() {
		analyze(200);
	}

	@Constraint(samples = 5, allowedPlus = 3500)
	public final void BAnalyzeFeatureModel0201() {
		analyze(201);
	}

	@Constraint(samples = 5, allowedPlus = 4000)
	public final void BAnalyzeFeatureModel0500() {
		analyze(500);
	}

	/************************************************************
	 * Analyzes constraints only
	 */
	private void BUpdateConstraints(final int i) {
		getFM(i).getAnalyser().updateConstraints();
	}

	@Constraint(samples = 5, allowedPlus = 1500)
	public final void BUpdateConstraints0001() {
		BUpdateConstraints(1);
	}

	@Constraint(samples = 5, allowedPlus = 1350)
	public final void BUpdateConstraints0002() {
		BUpdateConstraints(2);
	}

	@Constraint(samples = 5, allowedPlus = 1100)
	public final void BUpdateConstraints0010() {
		BUpdateConstraints(10);
	}

	@Constraint(samples = 5, allowedPlus = 1050)
	public final void BUpdateConstraints0020() {
		BUpdateConstraints(20);
	}

	@Constraint(samples = 5, allowedPlus = 1050)
	public final void BUpdateConstraints0021() {
		BUpdateConstraints(21);
	}

	@Constraint(samples = 5, allowedPlus = 1050)
	public final void BUpdateConstraints0050() {
		BUpdateConstraints(50);
	}

	@Constraint(samples = 5, allowedPlus = 1050)
	public final void BUpdateConstraints0100() {
		BUpdateConstraints(100);
	}

	@Constraint(samples = 5, allowedPlus = 1150)
	public final void BUpdateConstraints0200() {
		BUpdateConstraints(201);
	}

	@Constraint(samples = 5, allowedPlus = 1250)
	public final void BUpdateConstraints0201() {
		BUpdateConstraints(201);
	}

	@Constraint(samples = 5, allowedPlus = 2500)
	public final void BUpdateConstraints0500() {
		BUpdateConstraints(500);
	}

	@Constraint(samples = 5, allowedPlus = 5800)
	public final void BUpdateConstraints1000() {
		BUpdateConstraints(1000);
	}

	/************************************************************
	 * Analyzes features only
	 */
	private void BUpdateFeatures(final int i) {
		getFM(i).getAnalyser().updateFeatures();
	}

	@Constraint(samples = 5, allowedPlus = 1100)
	public final void BUpdateFeatures0001() {
		BUpdateFeatures(1);
	}

	@Constraint(samples = 5, allowedPlus = 1100)
	public final void BUpdateFeatures0002() {
		BUpdateFeatures(2);
	}

	@Constraint(samples = 5, allowedPlus = 1050)
	public final void BUpdateFeatures0010() {
		BUpdateFeatures(10);
	}

	@Constraint(samples = 5, allowedPlus = 1050)
	public final void BUpdateFeatures0020() {
		BUpdateFeatures(20);
	}

	@Constraint(samples = 5, allowedPlus = 1100)
	public final void BUpdateFeatures0021() {
		BUpdateFeatures(21);
	}

	@Constraint(samples = 5, allowedPlus = 1050)
	public final void BUpdateFeatures0050() {
		BUpdateFeatures(50);
	}

	@Constraint(samples = 5, allowedPlus = 1000)
	public final void BUpdateFeatures0100() {
		BUpdateFeatures(100);
	}

	@Constraint(samples = 5, allowedPlus = 1150)
	public final void BUpdateFeatures0200() {
		BUpdateFeatures(200);
	}

	@Constraint(samples = 5, allowedPlus = 3500)
	public final void BUpdateFeatures0201() {
		BUpdateFeatures(201);
	}

	@Constraint(samples = 5, allowedPlus = 1500)
	public final void BUpdateFeatures0500() {
		BUpdateFeatures(500);
	}

	@Constraint(samples = 5, allowedPlus = 2500)
	public final void BUpdateFeatures1000() {
		BUpdateFeatures(1000);
	}

	private static IFeatureModel getFM(final int i) {
		switch (i) {
		case 1:
			return Commons.loadBenchmarkFeatureModelFromFile("berkeley_db_model.xml");
		case 2:
			return Commons.loadBenchmarkFeatureModelFromFile("berkeley_db_model2.xml");
		case 1000:
			return Commons.loadBenchmarkFeatureModelFromFile("1000-100.xml");
		case 500:
			return Commons.loadBenchmarkFeatureModelFromFile("500-101.xml");
		case 200:
			return Commons.loadBenchmarkFeatureModelFromFile("200-100.xml");
		case 201:
			return Commons.loadBenchmarkFeatureModelFromFile("200-100-hidden.xml");
		case 100:
			return Commons.loadBenchmarkFeatureModelFromFile("100-100.xml");
		case 50:
			return Commons.loadBenchmarkFeatureModelFromFile("50-100.xml");
		case 20:
			return Commons.loadBenchmarkFeatureModelFromFile("20-100.xml");
		case 21:
			return Commons.loadBenchmarkFeatureModelFromFile("20-100-hidden.xml");
		case 10:
			return Commons.loadBenchmarkFeatureModelFromFile("10-100.xml");
		default:
			System.err.println("NO FM");
			return Commons.loadBenchmarkFeatureModelFromFile("10-100.xml");
		}
	}

}
