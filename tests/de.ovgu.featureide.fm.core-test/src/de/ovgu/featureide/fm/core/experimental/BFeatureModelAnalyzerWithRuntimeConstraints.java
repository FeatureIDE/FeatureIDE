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

import java.io.File;
import java.io.FileFilter;
import java.io.FileNotFoundException;
import java.util.HashMap;

import org.junit.Test;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;
import de.ovgu.jcorridore.RuntimeConstraint;
import de.ovgu.jcorridore.annotations.Constraint;
import de.ovgu.jcorridore.annotations.Record;

/**
 * This is a benchmark for analyzes at the {@link FeatureModel}.
 * The test cases do not analyze the validity of the analyses.
 * 
 * All timeouts are set to around 4 times the measured times(with intel i5 @ 3,3 GHz)
 * to avoid that the tests fail for slower computers.
 * 
 * @author Jens Meinicke
 */
public class BFeatureModelAnalyzerWithRuntimeConstraints {

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

	private static final FileFilter filter = new FileFilter() {
		@Override
		public boolean accept(final File pathname) {
			return pathname.getName().endsWith(".xml");
		}
	};

	private final static FeatureModel init(final String name) {
		FeatureModel fm = new FeatureModel();
		File modelFileFolder = getFolder();
		for (File f : modelFileFolder.listFiles(filter)) {
			if (f.getName().equals(name)) {
				try {
					new XmlFeatureModelReader(fm).readFromFile(f);
					break;
				} catch (FileNotFoundException e) {
					e.printStackTrace();
				} catch (UnsupportedModelException e) {
					e.printStackTrace();
				}
			}
		}
		return fm;
	}

	private static File getFolder() {
		File folder = new File("/home/itidbrun/TeamCity/buildAgent/work/featureide/tests/de.ovgu.featureide.fm.core-test/src/benchmarkFeatureModels/");
		if (!folder.canRead()) {
			folder = new File(ClassLoader.getSystemResource("benchmarkFeatureModels").getPath());
		}
		return folder;
	}

	/************************************************************
	 * Analyzes the model completely.
	 */
	private static void analyze(final int i) {
		getFM(i).getAnalyser().analyzeFeatureModel(null);
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1500)
	public final void BAnalyzeFeatureModel1() {
		if (RuntimeConstraint.inject(this.getClass())) {
			analyze(1);
		}
	}

	//	@Test
	//	@Record(samples = 5)
	//	@Constraint(samples = 5, allowedMedianDeviation = 500)
	//	public final void BAnalyzeFeatureModel1Ref() {
	//		if (RuntimeConstraint.inject(this.getClass())) {
	//			BAnalyzeFeatureModel18();
	//		}
	//	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1500)
	public final void BAnalyzeFeatureModel2() {
		if (RuntimeConstraint.inject(this.getClass())) {
			analyze(2);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1500)
	public final void BAnalyzeFeatureModel10() {
		if (RuntimeConstraint.inject(this.getClass())) {
			analyze(10);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1500)
	public final void BAnalyzeFeatureModel20() {
		if (RuntimeConstraint.inject(this.getClass())) {
			analyze(20);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1500)
	public final void BAnalyzeFeatureModel21() {
		if (RuntimeConstraint.inject(this.getClass())) {
			analyze(21);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1500)
	public final void BAnalyzeFeatureModel50() {
		if (RuntimeConstraint.inject(this.getClass())) {
			analyze(50);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1500)
	public final void BAnalyzeFeatureModel100() {
		if (RuntimeConstraint.inject(this.getClass())) {
			analyze(100);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 3200)
	public final void BAnalyzeFeatureModel200() {
		if (RuntimeConstraint.inject(this.getClass())) {
			analyze(200);
		}
	}

	@Test
	@Record(samples = 5, revision = 2)
	@Constraint(samples = 5, allowedMedianDeviation = 3500, revisionReference = 2)
	public final void BAnalyzeFeatureModel201() {
		if (RuntimeConstraint.inject(this.getClass())) {
			analyze(201);
		}
	}

	@Test
	@Record(samples = 5, revision = 2)
	@Constraint(samples = 5, allowedMedianDeviation = 4000, revisionReference = 2)
	public final void BAnalyzeFeatureModel500() {
		if (RuntimeConstraint.inject(this.getClass())) {
			analyze(500);
		}
	}

	/************************************************************
	 * Analyzes constraints only
	 */
	private void BUpdateConstraints(final int i) {
		getFM(i).getAnalyser().updateConstraints(new HashMap<Object, Object>(), new HashMap<Object, Object>());
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1500)
	public final void BUpdateConstraints1() {
		if (RuntimeConstraint.inject(this.getClass())) {
			BUpdateConstraints(1);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1350)
	public final void BUpdateConstraints2() {
		if (RuntimeConstraint.inject(this.getClass())) {
			BUpdateConstraints(2);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1100)
	public final void BUpdateConstraints10() {
		if (RuntimeConstraint.inject(this.getClass())) {
			BUpdateConstraints(10);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1050)
	public final void BUpdateConstraints20() {
		if (RuntimeConstraint.inject(this.getClass())) {
			BUpdateConstraints(20);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1050)
	public final void BUpdateConstraints21() {
		if (RuntimeConstraint.inject(this.getClass())) {
			BUpdateConstraints(21);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1050)
	public final void BUpdateConstraints50() {
		if (RuntimeConstraint.inject(this.getClass())) {
			BUpdateConstraints(50);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1050)
	public final void BUpdateConstraints100() {
		if (RuntimeConstraint.inject(this.getClass())) {
			BUpdateConstraints(100);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1150)
	public final void BUpdateConstraints200() {
		if (RuntimeConstraint.inject(this.getClass())) {
			BUpdateConstraints(201);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1250)
	public final void BUpdateConstraints201() {
		if (RuntimeConstraint.inject(this.getClass())) {
			BUpdateConstraints(201);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 2500)
	public final void BUpdateConstraints500() {
		if (RuntimeConstraint.inject(this.getClass())) {
			BUpdateConstraints(500);
		}
	}

	@Test
	@Record(samples = 5, revision = 2)
	@Constraint(samples = 5, allowedMedianDeviation = 5800, revisionReference = 2)
	public final void BUpdateConstraints1000() {
		if (RuntimeConstraint.inject(this.getClass())) {
			BUpdateConstraints(1000);
		}
	}

	/************************************************************
	 * Analyzes features only
	 */
	private void BUpdateFeatures(final int i) {
		getFM(i).getAnalyser().updateFeatures(new HashMap<Object, Object>(), new HashMap<Object, Object>());
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1100)
	public final void BUpdateFeatures1() {
		if (RuntimeConstraint.inject(this.getClass())) {
			BUpdateFeatures(1);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1100)
	public final void BUpdateFeatures2() {
		if (RuntimeConstraint.inject(this.getClass())) {
			BUpdateFeatures(2);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1050)
	public final void BUpdateFeatures10() {
		if (RuntimeConstraint.inject(this.getClass())) {
			BUpdateFeatures(10);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1050)
	public final void BUpdateFeatures20() {
		if (RuntimeConstraint.inject(this.getClass())) {
			BUpdateFeatures(20);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1100)
	public final void BUpdateFeatures21() {
		if (RuntimeConstraint.inject(this.getClass())) {
			BUpdateFeatures(21);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1050)
	public final void BUpdateFeatures50() {
		if (RuntimeConstraint.inject(this.getClass())) {
			BUpdateFeatures(50);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1000)
	public final void BUpdateFeatures100() {
		if (RuntimeConstraint.inject(this.getClass())) {
			BUpdateFeatures(100);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1150)
	public final void BUpdateFeatures200() {
		if (RuntimeConstraint.inject(this.getClass())) {
			BUpdateFeatures(200);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 3500)
	public final void BUpdateFeatures201() {
		if (RuntimeConstraint.inject(this.getClass())) {
			BUpdateFeatures(201);
		}
	}

	@Test
	@Record(samples = 5)
	@Constraint(samples = 5, allowedMedianDeviation = 1500)
	public final void BUpdateFeatures500() {
		if (RuntimeConstraint.inject(this.getClass())) {
			BUpdateFeatures(500);
		}
	}

	@Test
	@Record(samples = 5, revision = 2)
	@Constraint(samples = 5, allowedMedianDeviation = 2500, revisionReference = 2)
	public final void BUpdateFeatures1000() {
		if (RuntimeConstraint.inject(this.getClass())) {
			BUpdateFeatures(1000);
		}
	}

	private static FeatureModel getFM(final int i) {
		switch (i) {
		case 1:
			return init("berkeley_db_model.xml");
		case 2:
			return init("berkeley_db_model2.xml");
		case 1000:
			return init("1000-100.xml");
		case 500:
			return init("500-101.xml");
		case 200:
			return init("200-100.xml");
		case 201:
			return init("200-100-hidden.xml");
		case 100:
			return init("100-100.xml");
		case 50:
			return init("50-100.xml");
		case 20:
			return init("20-100.xml");
		case 21:
			return init("20-100-hidden.xml");
		case 10:
			return init("10-100.xml");
		default:
			System.err.println("NO FM");
			return init("10-100.xml");
		}
	}

}
