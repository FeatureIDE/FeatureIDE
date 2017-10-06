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
package de.ovgu.featureide.fm.core;

import org.junit.Test;

import de.ovgu.featureide.Commons;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * This is a benchmark for analyzes at the {@link IFeatureModel}. The test cases do not analyze the validity of the analyses.
 *
 * All timeouts are set to around 4 times the measured times(with intel i5 @ 3,3 GHz) to avoid that the tests fail for slower computers.
 *
 * @author Jens Meinicke
 */
public class BFeatureModelAnalyzer {

	/**
	 * Warm up the analyzer to prevent unpredictable timeout exceptions.
	 */
	static {
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

	@Test(timeout = 6000) // 0.749s @ i5(3,3GHz)
	public final void BAnalyzeFeatureModel1() {
		analyze(1);
	}

	@Test(timeout = 2500) // 0.385s @ i5(3,3GHz)
	public final void BAnalyzeFeatureModel2() {
		analyze(2);
	}

	@Test(timeout = 100) // 0.007 @ i5(3,3GHz)
	public final void BAnalyzeFeatureModel10() {
		analyze(10);
	}

	@Test(timeout = 100) // 0.006s @ i5(3,3GHz)
	public final void BAnalyzeFeatureModel20() {
		analyze(20);
	}

	@Test(timeout = 250) // 0.020s @ i5(3,3GHz)
	public final void BAnalyzeFeatureModel21() {
		analyze(21);
	}

	@Test(timeout = 1000) // 0.036 @ i5(3,3GHz)
	public final void BAnalyzeFeatureModel50() {
		analyze(50);
	}

	@Test(timeout = 2500) // 0.142s @ i5(3,3GHz)
	public final void BAnalyzeFeatureModel100() {
		analyze(100);
	}

	@Test(timeout = 8000) // 0.886s @ i5(3,3GHz)
	public final void BAnalyzeFeatureModel200() {
		analyze(200);
	}

	@Test(timeout = 22000) // 5.519s @ i5(3,3GHz)
	public final void BAnalyzeFeatureModel201() {
		analyze(201);
	}

	@Test(timeout = 30000) // 6.147s @ i5(3,3GHz)
	public final void BAnalyzeFeatureModel500() {
		analyze(500);
	}

//	@Test (timeout=300000) // 75.904s @ i5(3,3GHz)
//	public void BAnalyzeFeatureModel1000() {
//		analyze(1000);
//	}

	/************************************************************
	 * Analyzes constraints only
	 */
	private void BUpdateConstraints(final int i) {
		getFM(i).getAnalyser().updateConstraints();
	}

	@Test(timeout = 2500) // 0.509 @ i5(3,3GHz)
	public final void BUpdateConstraints1() {
		BUpdateConstraints(1);
	}

	@Test(timeout = 1500) // 0.328 @ i5(3,3GHz)
	public final void BUpdateConstraints2() {
		BUpdateConstraints(2);
	}

	@Test(timeout = 100) // 0.004s @ i5(3,3GHz)
	public final void BUpdateConstraints10() {
		BUpdateConstraints(10);
	}

	@Test(timeout = 100) // 0.005s @ i5(3,3GHz)
	public final void BUpdateConstraints20() {
		BUpdateConstraints(20);
	}

	@Test(timeout = 100) // 0.004s @ i5(3,3GHz)
	public final void BUpdateConstraints21() {
		BUpdateConstraints(21);
	}

	@Test(timeout = 100) // 0.011s @ i5(3,3GHz)
	public final void BUpdateConstraints50() {
		BUpdateConstraints(50);
	}

	@Test(timeout = 250) // 0.051s @ i5(3,3GHz)
	public final void BUpdateConstraints100() {
		BUpdateConstraints(100);
	}

	@Test(timeout = 1500) // 0.233s @ i5(3,3GHz)
	public final void BUpdateConstraints200() {
		BUpdateConstraints(201);
	}

	@Test(timeout = 1500) // 0.232s @ i5(3,3GHz)
	public final void BUpdateConstraints201() {
		BUpdateConstraints(201);
	}

	@Test(timeout = 10000) // 1.809s @ i5(3,3GHz)
	public final void BUpdateConstraints500() {
		BUpdateConstraints(500);
	}

//	@Test (timeout=140000) //  @ i5(3,3GHz)
	public final void BUpdateConstraints1000() {
		BUpdateConstraints(1000);
	}

	/************************************************************
	 * Analyzes features only
	 */
	private void BUpdateFeatures(final int i) {
		getFM(i).getAnalyser().updateFeatures();
	}

	@Test(timeout = 1000) // 0.053s @ i5(3,3GHz)
	public final void BUpdateFeatures1() {
		BUpdateFeatures(1);
	}

	@Test(timeout = 1000) // 0.056s @ i5(3,3GHz)
	public final void BUpdateFeatures2() {
		BUpdateFeatures(2);
	}

	@Test(timeout = 100) // 0.005s @ i5(3,3GHz)
	public final void BUpdateFeatures10() {
		BUpdateFeatures(10);
	}

	@Test(timeout = 100) // 0.005s @ i5(3,3GHz)
	public final void BUpdateFeatures20() {
		BUpdateFeatures(20);
	}

	@Test(timeout = 200) // 0.020s @ i5(3,3GHz)
	public final void BUpdateFeatures21() {
		BUpdateFeatures(21);
	}

	@Test(timeout = 250) // 0.012s @ i5(3,3GHz)
	public final void BUpdateFeatures50() {
		BUpdateFeatures(50);
	}

	@Test(timeout = 200) // 0.027s @ i5(3,3GHz)
	public final void BUpdateFeatures100() {
		BUpdateFeatures(100);
	}

	@Test(timeout = 500) // 0.092s @ i5(3,3GHz)
	public final void BUpdateFeatures200() {
		BUpdateFeatures(200);
	}

	@Test(timeout = 16000) // 5.446s @ i5(3,3GHz)
	public final void BUpdateFeatures201() {
		BUpdateFeatures(201);
	}

	@Test(timeout = 2500) // 0,465s @ i5(3,3GHz)
	public final void BUpdateFeatures500() {
		BUpdateFeatures(500);
	}

	@Test(timeout = 10000) // 2,925s @ i5(3,3GHz)
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
