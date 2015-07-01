/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.HashMap;

import de.ovgu.featureide.common.Commons;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.runtimetest.RuntimeTest;
import de.ovgu.runtimetest.RuntimeTest.Annotations.Constraint;
import de.ovgu.runtimetest.RuntimeTest.Annotations.WarmUp;

/**
 * This is a benchmark for analyzes at the {@link FeatureModel}.
 * The test cases do not analyze the validity of the analyses.
 * 
 * All timeouts are set to around 4 times the measured times(with intel i5 @ 3,3 GHz)
 * to avoid that the tests fail for slower computers.
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
	public final void BAnalyzeFeatureModel1() {
		analyze(1);
	}

	@Constraint(samples = 5, allowedPlus = 1500)
	public final void BAnalyzeFeatureModel2() {
		analyze(2);
	}

	@Constraint(samples = 5, allowedPlus = 1500)
	public final void BAnalyzeFeatureModel10() {
		analyze(10);
	}

	@Constraint(samples = 5, allowedPlus = 1500)
	public final void BAnalyzeFeatureModel20() {
		analyze(20);
	}

	@Constraint(samples = 5, allowedPlus = 1500)
	public final void BAnalyzeFeatureModel21() {
		analyze(21);
	}

	@Constraint(samples = 5, allowedPlus = 1500)
	public final void BAnalyzeFeatureModel50() {
		analyze(50);
	}

	@Constraint(samples = 5, allowedPlus = 1500)
	public final void BAnalyzeFeatureModel100() {
		analyze(100);
	}

	@Constraint(samples = 5, allowedPlus = 3200)
	public final void BAnalyzeFeatureModel200() {
		analyze(200);
	}

	@Constraint(samples = 5, allowedPlus = 3500)
	public final void BAnalyzeFeatureModel201() {
		analyze(201);
	}

	@Constraint(samples = 5, allowedPlus = 4000)
	public final void BAnalyzeFeatureModel500() {
		analyze(500);
	}

	/************************************************************
	 * Analyzes constraints only
	 */
	private void BUpdateConstraints(final int i) {
		getFM(i).getAnalyser().updateConstraints(new HashMap<Object, Object>(), new HashMap<Object, Object>());
	}

	@Constraint(samples = 5, allowedPlus = 1500)
	public final void BUpdateConstraints1() {
		BUpdateConstraints(1);
	}

	@Constraint(samples = 5, allowedPlus = 1350)
	public final void BUpdateConstraints2() {
		BUpdateConstraints(2);
	}

	@Constraint(samples = 5, allowedPlus = 1100)
	public final void BUpdateConstraints10() {
		BUpdateConstraints(10);
	}

	@Constraint(samples = 5, allowedPlus = 1050)
	public final void BUpdateConstraints20() {
		BUpdateConstraints(20);
	}

	@Constraint(samples = 5, allowedPlus = 1050)
	public final void BUpdateConstraints21() {
		BUpdateConstraints(21);
	}

	@Constraint(samples = 5, allowedPlus = 1050)
	public final void BUpdateConstraints50() {
		BUpdateConstraints(50);
	}

	@Constraint(samples = 5, allowedPlus = 1050)
	public final void BUpdateConstraints100() {
		BUpdateConstraints(100);
	}

	@Constraint(samples = 5, allowedPlus = 1150)
	public final void BUpdateConstraints200() {
		BUpdateConstraints(201);
	}

	@Constraint(samples = 5, allowedPlus = 1250)
	public final void BUpdateConstraints201() {
		BUpdateConstraints(201);
	}

	@Constraint(samples = 5, allowedPlus = 2500)
	public final void BUpdateConstraints500() {
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
		getFM(i).getAnalyser().updateFeatures(new HashMap<Object, Object>(), new HashMap<Object, Object>());
	}

	@Constraint(samples = 5, allowedPlus = 1100)
	public final void BUpdateFeatures1() {
		BUpdateFeatures(1);
	}

	@Constraint(samples = 5, allowedPlus = 1100)
	public final void BUpdateFeatures2() {
		BUpdateFeatures(2);
	}

	@Constraint(samples = 5, allowedPlus = 1050)
	public final void BUpdateFeatures10() {
		BUpdateFeatures(10);
	}

	@Constraint(samples = 5, allowedPlus = 1050)
	public final void BUpdateFeatures20() {
		BUpdateFeatures(20);
	}

	@Constraint(samples = 5, allowedPlus = 1100)
	public final void BUpdateFeatures21() {
		BUpdateFeatures(21);
	}

	@Constraint(samples = 5, allowedPlus = 1050)
	public final void BUpdateFeatures50() {
		BUpdateFeatures(50);
	}

	@Constraint(samples = 5, allowedPlus = 1000)
	public final void BUpdateFeatures100() {
		BUpdateFeatures(100);
	}

	@Constraint(samples = 5, allowedPlus = 1150)
	public final void BUpdateFeatures200() {
		BUpdateFeatures(200);
	}

	@Constraint(samples = 5, allowedPlus = 3500)
	public final void BUpdateFeatures201() {
		BUpdateFeatures(201);
	}

	@Constraint(samples = 5, allowedPlus = 1500)
	public final void BUpdateFeatures500() {
		BUpdateFeatures(500);
	}

	@Constraint(samples = 5, allowedPlus = 2500)
	public final void BUpdateFeatures1000() {
		BUpdateFeatures(1000);
	}

	private static FeatureModel getFM(final int i) {
		switch (i) {
		case 1:
			return Commons.loadFeatureModelFromFile("berkeley_db_model.xml", Commons.FEATURE_MODEL_BENCHMARK_PATH_REMOTE, Commons.FEATURE_MODEL_BENCHMARK_PATH_LOCAL_CLASS_PATH);
		case 2:
			return Commons.loadFeatureModelFromFile("berkeley_db_model2.xml", Commons.FEATURE_MODEL_BENCHMARK_PATH_REMOTE, Commons.FEATURE_MODEL_BENCHMARK_PATH_LOCAL_CLASS_PATH);
		case 1000:
			return Commons.loadFeatureModelFromFile("1000-100.xml", Commons.FEATURE_MODEL_BENCHMARK_PATH_REMOTE, Commons.FEATURE_MODEL_BENCHMARK_PATH_LOCAL_CLASS_PATH);
		case 500:
			return Commons.loadFeatureModelFromFile("500-101.xml", Commons.FEATURE_MODEL_BENCHMARK_PATH_REMOTE, Commons.FEATURE_MODEL_BENCHMARK_PATH_LOCAL_CLASS_PATH);
		case 200:
			return Commons.loadFeatureModelFromFile("200-100.xml", Commons.FEATURE_MODEL_BENCHMARK_PATH_REMOTE, Commons.FEATURE_MODEL_BENCHMARK_PATH_LOCAL_CLASS_PATH);
		case 201:
			return Commons.loadFeatureModelFromFile("200-100-hidden.xml", Commons.FEATURE_MODEL_BENCHMARK_PATH_REMOTE, Commons.FEATURE_MODEL_BENCHMARK_PATH_LOCAL_CLASS_PATH);
		case 100:
			return Commons.loadFeatureModelFromFile("100-100.xml", Commons.FEATURE_MODEL_BENCHMARK_PATH_REMOTE, Commons.FEATURE_MODEL_BENCHMARK_PATH_LOCAL_CLASS_PATH);
		case 50:
			return Commons.loadFeatureModelFromFile("50-100.xml", Commons.FEATURE_MODEL_BENCHMARK_PATH_REMOTE, Commons.FEATURE_MODEL_BENCHMARK_PATH_LOCAL_CLASS_PATH);
		case 20:
			return Commons.loadFeatureModelFromFile("20-100.xml", Commons.FEATURE_MODEL_BENCHMARK_PATH_REMOTE, Commons.FEATURE_MODEL_BENCHMARK_PATH_LOCAL_CLASS_PATH);
		case 21:
			return Commons.loadFeatureModelFromFile("20-100-hidden.xml", Commons.FEATURE_MODEL_BENCHMARK_PATH_REMOTE, Commons.FEATURE_MODEL_BENCHMARK_PATH_LOCAL_CLASS_PATH);
		case 10:
			return Commons.loadFeatureModelFromFile("10-100.xml", Commons.FEATURE_MODEL_BENCHMARK_PATH_REMOTE, Commons.FEATURE_MODEL_BENCHMARK_PATH_LOCAL_CLASS_PATH);
		default:
			System.err.println("NO FM");
			return Commons.loadFeatureModelFromFile("10-100.xml", Commons.FEATURE_MODEL_BENCHMARK_PATH_REMOTE, Commons.FEATURE_MODEL_BENCHMARK_PATH_LOCAL_CLASS_PATH);
		}
	}

}
