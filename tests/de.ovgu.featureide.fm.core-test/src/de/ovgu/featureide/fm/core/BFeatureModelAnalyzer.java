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

import org.jbenchx.annotations.Bench;
import org.jbenchx.annotations.ForEachInt;

import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;

/**
 * This is a benchmark for analyzes at the {@link FeatureModel}<br> 
 * To run this benchmark you need the plug-in JBenchX. 
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
	
	private FeatureModel fm100_100 = init("100-100.xml");
	
	private FeatureModel fm50_100 = init("50-100.xml");
	
	private FeatureModel fm20_100 = init("20-100.xml");
	
	private FeatureModel fm10_100 = init("10-100.xml");
	
	private final FeatureModel init(String name) {
		FeatureModel fm = new FeatureModel();
		File MODEL_FILE_FOLDER = new File(ClassLoader.getSystemResource(
				"benchmarkFeatureModels").getPath());
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

	/**
	 * Calculates the full duration of analyzing the feature model.
	 */
	@Bench //(maxRunCount = 1) // For 500 and higher it is not practicable to calculate a more precise value
	public void BAnalyzeFeatureModel(@ForEachInt({1, 2, 10, 20, 50, 100, 200, /*500, 1000*/}) int i) {
		getFM(i).getAnalyser().analyzeFeatureModel(null);
	}
	
	/**
	 * Calculates the duration of analyzing constraints
	 */
	@Bench (maxRunCount = 1)
	public void BUpdateConstraints(@ForEachInt({1, 2, 10, 20, 50, 100, 200, 500}) int i) {
		getFM(i).getAnalyser().updateConstraints(new HashMap<Object, Object>(), new HashMap<Object, Object>());
	}
	
	/**
	 * Calculates the duration of analyzing features
	 */
	@Bench (maxRunCount = 1)
	public void BUpdateFeatures(@ForEachInt({1, 2, 10, 20, 50, 100, 200, 500}) int i) {
		getFM(i).getAnalyser().updateFeatures(new HashMap<Object, Object>(), new HashMap<Object, Object>());
	}
	
	@Bench
	public void clone(@ForEachInt({1,2,10,20,50,100,200, 500, 1000}) int i) {
		getFM(i).clone();
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
		case 50 :
			return fm50_100;
		case 100 :
			return fm100_100;
		case 200 :
			return fm200_100;
		case 500 :
			return fm500_100;
		case 1000 :
			return fm1000_100;
		case 10000 :
			return fm10000_100;
		default:
			System.err.println("NO FM");
			return berkeley_1;
		}
	}
	
}
