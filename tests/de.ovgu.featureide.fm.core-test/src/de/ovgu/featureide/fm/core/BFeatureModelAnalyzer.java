/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.fm.core;

import java.io.File;
import java.io.FileFilter;
import java.io.FileNotFoundException;
import java.util.HashMap;

import org.junit.Test;

import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;

/**
 * This is a benchmark for analyzes at the {@link FeatureModel}
 *  
 * @author Jens Meinicke
 */
public class BFeatureModelAnalyzer {
	
	private static final FileFilter filter = new FileFilter() {
		@Override
		public boolean accept(File pathname) {
			return pathname.getName().endsWith(".xml");
		}
	};
	
	private FeatureModel berkeley_1 = init("berkeley_db_model.xml");
	
	/** The same model without the dead causing constraint */
	private FeatureModel berkeley_2 = init("berkeley_db_model2.xml");
	
	/** 
	 * A great model with 10000 Features and many constraints
	 * This model seems to be to large for analysis 
	 */
	private FeatureModel fm10000_100 = init("10000-100.xml");

	private FeatureModel fm1000_100 = init("1000-100.xml");
	
	private FeatureModel fm500_100 = init("500-100.xml");
	
	private FeatureModel fm200_100 = init("200-100.xml");
	
	/**
	 * A copy if 200-100.xml with some random hidden features.
	 */
	private FeatureModel fm200_100_hidden = init("200-100-hidden.xml");
	
	private FeatureModel fm100_100 = init("100-100.xml");
	
	private FeatureModel fm50_100 = init("50-100.xml");
	
	private FeatureModel fm20_100 = init("20-100.xml");

	/**
	 * A copy if 20-100.xml with some random hidden features.
	 */
	private FeatureModel fm20_100_hidden = init("20-100-hidden.xml");
	
	private FeatureModel fm10_100 = init("10-100.xml");
	
	private final FeatureModel init(String name) {
		FeatureModel fm = new FeatureModel();
		File MODEL_FILE_FOLDER = getFolder();
		for (File f : MODEL_FILE_FOLDER.listFiles(filter)) {
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
		File folder =  new File("/vol1/teamcity_itidb/TeamCity/buildAgent/work/featureide/tests/de.ovgu.featureide.fm.core-test/src/benchmarkFeatureModels/"); 
		if (!folder.canRead()) { 
			folder = new File(ClassLoader.getSystemResource("benchmarkFeatureModels").getPath()); 
		} 
		return folder; 
	}

	/**
	 * Analyzes the model completely.
	 */
	private void analyze(int i) {
		getFM(i).getAnalyser().analyzeFeatureModel(null);
	}

	@Test (timeout=20000) // 6,377s @ i5(3,3GHz)
	public void BAnalyzeFeatureModel1() {
		analyze(1);
	}

	@Test (timeout=6000) // 1,210s @ i5(3,3GHz)
	public void BAnalyzeFeatureModel2() {
		analyze(2);
	}
	
	@Test (timeout=2000) // 0,310s @ i5(3,3GHz)
	public void BAnalyzeFeatureModel10() {
		analyze(10);
	}
	
	@Test (timeout=2000) // 0,315s @ i5(3,3GHz)
	public void BAnalyzeFeatureModel20() {
		analyze(20);
	}
	
	@Test (timeout=2000) // 0,330s @ i5(3,3GHz)
	public void BAnalyzeFeatureModel21() {
		analyze(21);
	}
	
	@Test (timeout=2000) // 0,375s @ i5(3,3GHz)
	public void BAnalyzeFeatureModel50() {
		analyze(50);
	}
	
	@Test (timeout=4000) // 0,799s @ i5(3,3GHz)
	public void BAnalyzeFeatureModel100() {
		analyze(100);
	}
	
	@Test (timeout=12000) // 3,812s @ i5(3,3GHz)
	public void BAnalyzeFeatureModel200() {
		analyze(200);
	}
	
	@Test (timeout=50000) // 11,183s @ i5(3,3GHz)
	public void BAnalyzeFeatureModel201() {
		analyze(201);
	}
	
	//@Test (timeout=200000) // 53,082s @ i5(3,3GHz)
	public void BAnalyzeFeatureModel500() {
		analyze(500);
	}
	
	/**
	 * Analyzes constraints only
	 */
	private void BUpdateConstraints(int i) {
		getFM(i).getAnalyser().updateConstraints(new HashMap<Object, Object>(), new HashMap<Object, Object>());
	}
	
	@Test (timeout=5000) // 1,356s @ i5(3,3GHz)
	public void BUpdateConstraints1() {
		BUpdateConstraints(1);
	}
	
	@Test (timeout=5000) // 1,184s @ i5(3,3GHz)
	public void BUpdateConstraints2() {
		BUpdateConstraints(2);
	}
	
	@Test (timeout=2000) // 0,325s @ i5(3,3GHz)
	public void BUpdateConstraints10() {
		BUpdateConstraints(10);
	}
	
	@Test (timeout=2000) // 0,324s @ i5(3,3GHz)
	public void BUpdateConstraints20() {
		BUpdateConstraints(20);
	}
	
	@Test (timeout=2000) // 0,329s @ i5(3,3GHz)
	public void BUpdateConstraints21() {
		BUpdateConstraints(21);
	}
	
	@Test (timeout=2000) // 0,342s @ i5(3,3GHz)
	public void BUpdateConstraints50() {
		BUpdateConstraints(50);
	}
	
	@Test (timeout=2000) // 0,425s @ i5(3,3GHz)
	public void BUpdateConstraints100() {
		BUpdateConstraints(100);
	}
	
	@Test (timeout=3000) // 0,850s @ i5(3,3GHz)
	public void BUpdateConstraints200() {
		BUpdateConstraints(201);
	}
	
	@Test (timeout=3000) // 0,847s @ i5(3,3GHz)
	public void BUpdateConstraints201() {
		BUpdateConstraints(201);
	}
	
	//@Test (timeout=50000) // 11,091s @ i5(3,3GHz)
	public void BUpdateConstraints500() {
		BUpdateConstraints(500);
	}
	
	/**
	 * Analyzes features only
	 */
	private void BUpdateFeatures(int i) {
		getFM(i).getAnalyser().updateFeatures(new HashMap<Object, Object>(), new HashMap<Object, Object>());
	}
	
	@Test (timeout=2000) // 0,421s @ i5(3,3GHz)
	public void BUpdateFeaturess1() {
		BUpdateFeatures(1);
	}
	
	@Test (timeout=2000) // 0,419s @ i5(3,3GHz)
	public void BUpdateFeatures2() {
		BUpdateFeatures(2);
	}
	
	@Test (timeout=2000) // 0,309s @ i5(3,3GHz)
	public void BUpdateFeatures10() {
		BUpdateFeatures(10);
	}
	
	@Test (timeout=2000) // 0,311s @ i5(3,3GHz)
	public void BUpdateFeatures20() {
		BUpdateFeatures(20);
	}
	
	@Test (timeout=2000) // 0,323s @ i5(3,3GHz)
	public void BUpdateFeatures21() {
		BUpdateFeatures(21);
	}
	
	@Test (timeout=2000) // 0,319s @ i5(3,3GHz)
	public void BUpdateFeatures50() {
		BUpdateFeatures(50);
	}
	
	@Test (timeout=2000) // 0,347s @ i5(3,3GHz)
	public void BUpdateFeatures100() {
		BUpdateFeatures(100);
	}
	
	@Test (timeout=2000) // 0,473s @ i5(3,3GHz)
	public void BUpdateFeatures200() {
		BUpdateFeatures(200);
	}
	
	@Test (timeout=30000) // 8,077s @ i5(3,3GHz)
	public void BUpdateFeatures201() {
		BUpdateFeatures(201);
	}
	
	@Test (timeout=4000) // 0,934s @ i5(3,3GHz)
	public void BUpdateFeatures500() {
		BUpdateFeatures(500);
	}

	/**
	 * @param i
	 * @return
	 */
	private FeatureModel getFM(int i) {
		switch (i) {
		case 1:
			return berkeley_1;
		case 2 :
			return berkeley_2;
		case 10 :
			return fm10_100;
		case 20 :
			return fm20_100;
		case 21 :
			return fm20_100_hidden;
		case 50 :
			return fm50_100;
		case 100 :
			return fm100_100;
		case 200 :
			return fm200_100;
		case 201 :
			return fm200_100_hidden;
		case 500 :
			return fm500_100;
		case 1000 :
			return fm1000_100;
		case 10000 :
			return fm10000_100;
		default:
			System.err.println("NO FM");
			return fm10_100;
		}
	}
	
}
