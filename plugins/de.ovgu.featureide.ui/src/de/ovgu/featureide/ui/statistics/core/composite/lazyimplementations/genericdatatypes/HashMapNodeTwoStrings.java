/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes;

import java.util.HashMap;

/**
 * Node in the statistics view to show lines of code. 
 * 
 * @author Schleicher Miro
 * @author Maximilian Homann
 * @author Philipp Kuhn
 */
public class HashMapNodeTwoStrings extends AbstractSortModeNode {

	protected HashMap<String, Integer> extensionFeatureLOCList = new HashMap<String, Integer>();
	protected HashMap<String, Integer> locCount = new HashMap<String, Integer>();
	protected HashMap<String, Integer> extensionFileLOCList = new HashMap<String, Integer>();
	/* 
	 * child 1: LOC by extension
	 * child 2: LOC by feature
	 * child 3: LOC by file
	 */
	protected int childIndex;

	/**
	 * Create a new <> to display either a <br>
	 * LOC by extension tree entry (child index 1)<br>
	 * LOC by feature tree entry (child index 2)<br>
	 * LOC by file tree entry (child index 3)
	 * @param description
	 * @param childIndex specifies the type of entry
	 * @param extList 
	 * @param extensionFileLOCList
	 */
	public HashMapNodeTwoStrings(String description, int childIndex, HashMap<String, Integer> extList,
			HashMap<String, Integer> extensionFileLOCList) {
		super(description);
		extensionFeatureLOCList = extList;
		this.childIndex = childIndex;
		this.extensionFileLOCList = extensionFileLOCList;
	}
	
	/**
	 * Create a new <> to display either a <br>
	 * LOC by extension tree entry (child index 1)<br>
	 * LOC by feature tree entry (child index 2)<br>
	 * LOC by file tree entry (child index 3)
	 * @param description
	 * @param locCount legacy super constructor
	 * @param childIndex specifies the type of entry
	 * @param extList 
	 * @param extensionFileLOCList
	 */
	public HashMapNodeTwoStrings(String description, int locCount, int childIndex, HashMap<String, Integer> extList,
			HashMap<String, Integer> extensionFileLOCList) {
		super(description, locCount);
		extensionFeatureLOCList = extList;
		this.childIndex = childIndex;
		this.extensionFileLOCList = extensionFileLOCList;
	}

	@Override
	protected void initChildren() {
		//LOC by extension
		if (childIndex == 1) {
			for (String extAndFeature : extensionFeatureLOCList.keySet()) {
				String extensionName = extAndFeature.split("#")[0];
				if (!locCount.containsKey(extensionName)) {
					locCount.put(extensionName, extensionFeatureLOCList.get(extAndFeature));
				} else {
					locCount.put(extensionName, locCount.get(extensionName) + extensionFeatureLOCList.get(extAndFeature));
				}
			}
		//LOC by feature
		} else if (childIndex == 2) {
			for (String extAndFeature : extensionFeatureLOCList.keySet()) {
				String featureName = extAndFeature.split("#")[1];
				if (!locCount.containsKey(featureName)) {
					locCount.put(featureName, extensionFeatureLOCList.get(extAndFeature));
				} else {
					locCount.put(featureName, locCount.get(featureName) + extensionFeatureLOCList.get(extAndFeature));
				}
			}
		//LOC by file	
		} else if (childIndex == 3) {
			for (String extAndFile: extensionFileLOCList.keySet()) {
				String fileName = extAndFile.split("#")[0];
				
				if(!locCount.containsKey(fileName)) {
					locCount.put(fileName, extensionFileLOCList.get(extAndFile));
				} else {
					locCount.put(fileName, locCount.get(fileName) + extensionFileLOCList.get(extAndFile));
				}
			}
		}
		
		for (String key : locCount.keySet()) {
			addChild(new HashMapNodeTwoStringsSub(key, locCount.get(key), childIndex, extensionFeatureLOCList, extensionFileLOCList));
		}

	}

}
