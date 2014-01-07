/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * This is a benchmark for analyzes at the {@link FeatureModel}.
 * The test cases do not analyze the validity of the analyses.
 * 
 * All timeouts are set to around 4 times the measured times(with intel i5 @ 3,3 GHz)
 * to avoid that the tests fail for slower computers. 
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

	/************************************************************
	 * Analyzes the model completely.
	 */
	private void analyze(int i) {
		getFM(i).getAnalyser().analyzeFeatureModel(null);
	}

	@Test (timeout=6000) // 1,378s @ i5(3,3GHz)
	public void BAnalyzeFeatureModel1() {
		analyze(1);
	}

	@Test (timeout=2500) // 0,446s @ i5(3,3GHz)
	public void BAnalyzeFeatureModel2() {
		analyze(2);
	}
	
	@Test (timeout=1000) // 0,055s @ i5(3,3GHz)
	public void BAnalyzeFeatureModel10() {
		analyze(10);
	}
	
	@Test (timeout=1000) // 0,056s @ i5(3,3GHz)
	public void BAnalyzeFeatureModel20() {
		analyze(20);
	}
	
	@Test (timeout=1000) // 0,070s @ i5(3,3GHz)
	public void BAnalyzeFeatureModel21() {
		analyze(21);
	}
	
	@Test (timeout=1000) // 0,086s @ i5(3,3GHz)
	public void BAnalyzeFeatureModel50() {
		analyze(50);
	}
	
	@Test (timeout=2000) // 0,227s @ i5(3,3GHz)
	public void BAnalyzeFeatureModel100() {
		analyze(100);
	}
	
	@Test (timeout=4500) // 1,001s @ i5(3,3GHz)
	public void BAnalyzeFeatureModel200() {
		analyze(200);
	}
	
	@Test (timeout=22000) // 4,380s @ i5(3,3GHz)
	public void BAnalyzeFeatureModel201() {
		analyze(201);
	}
	
	@Test (timeout=36000) // 8,172s @ i5(3,3GHz)
	public void BAnalyzeFeatureModel500() {
		analyze(500);
	}
	
//	@Test (timeout=300000) // 86,968s @ i5(3,3GHz)
	public void BAnalyzeFeatureModel1000() {
		analyze(1000);
	}
	
//	@Test //(timeout=1000000) // ?s @ i5(3,3GHz)
	public void BAnalyzeFeatureModel10000() {
		analyze(10000);
	}
	
	/************************************************************
	 * Analyzes constraints only
	 */
	private void BUpdateConstraints(int i) {
		getFM(i).getAnalyser().updateConstraints(new HashMap<Object, Object>(), new HashMap<Object, Object>());
	}
	
	@Test (timeout=2000) // 0,367s @ i5(3,3GHz)
	public void BUpdateConstraints1() {
		BUpdateConstraints(1);
	}
	
	@Test (timeout=2000) // 0,342s @ i5(3,3GHz)
	public void BUpdateConstraints2() {
		BUpdateConstraints(2);
	}
	
	@Test (timeout=800) // 0,050s @ i5(3,3GHz)
	public void BUpdateConstraints10() {
		BUpdateConstraints(10);
	}
	
	@Test (timeout=800) // 0,049s @ i5(3,3GHz)
	public void BUpdateConstraints20() {
		BUpdateConstraints(20);
	}
	
	@Test (timeout=800) // 0,050s @ i5(3,3GHz)
	public void BUpdateConstraints21() {
		BUpdateConstraints(21);
	}
	
	@Test (timeout=1000) // 0,055s @ i5(3,3GHz)
	public void BUpdateConstraints50() {
		BUpdateConstraints(50);
	}
	
	@Test (timeout=1000) // 0,092s @ i5(3,3GHz)
	public void BUpdateConstraints100() {
		BUpdateConstraints(100);
	}
	
	@Test (timeout=1600) // 0,254s @ i5(3,3GHz)
	public void BUpdateConstraints200() {
		BUpdateConstraints(201);
	}
	
	@Test (timeout=1600) // 0,290s @ i5(3,3GHz)
	public void BUpdateConstraints201() {
		BUpdateConstraints(201);
	}
	
	@Test (timeout=16000) // 3,739s @ i5(3,3GHz)
	public void BUpdateConstraints500() {
		BUpdateConstraints(500);
	}
	
//	@Test (timeout=140000) // 29,846s @ i5(3,3GHz)
	public void BUpdateConstraints1000() {
		BUpdateConstraints(1000);
	}
	
	/************************************************************
	 * Analyzes features only
	 */
	private void BUpdateFeatures(int i) {
		getFM(i).getAnalyser().updateFeatures(new HashMap<Object, Object>(), new HashMap<Object, Object>());
	}
	
	@Test (timeout=1000) // 0,098 @ i5(3,3GHz)
	public void BUpdateFeaturess1() {
		BUpdateFeatures(1);
	}
	
	@Test (timeout=1000) // 0,098s @ i5(3,3GHz)
	public void BUpdateFeatures2() {
		BUpdateFeatures(2);
	}
	
	@Test (timeout=800) // 0,048s @ i5(3,3GHz)
	public void BUpdateFeatures10() {
		BUpdateFeatures(10);
	}
	
	@Test (timeout=800) // 0,049s @ i5(3,3GHz)
	public void BUpdateFeatures20() {
		BUpdateFeatures(20);
	}
	
	@Test (timeout=800) // 0,061s @ i5(3,3GHz)
	public void BUpdateFeatures21() {
		BUpdateFeatures(21);
	}
	
	@Test (timeout=800) // 0,054s @ i5(3,3GHz)
	public void BUpdateFeatures50() {
		BUpdateFeatures(50);
	}
	
	@Test (timeout=800) // 0,071s @ i5(3,3GHz)
	public void BUpdateFeatures100() {
		BUpdateFeatures(100);
	}
	
	@Test (timeout=1200) // 0,143s @ i5(3,3GHz)
	public void BUpdateFeatures200() {
		BUpdateFeatures(200);
	}
	
	@Test (timeout=16000) // 3718s @ i5(3,3GHz)
	public void BUpdateFeatures201() {
		BUpdateFeatures(201);
	}
	
	@Test (timeout=2800) // 0,474s @ i5(3,3GHz)
	public void BUpdateFeatures500() {
		BUpdateFeatures(500);
	}
	
	@Test (timeout=10000) // 2,121s @ i5(3,3GHz)
	public void BUpdateFeatures1000() {
		BUpdateFeatures(1000);
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
