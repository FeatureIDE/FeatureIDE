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

	private HashMap<String, Integer> extensionFeatureLOCList = new HashMap<String, Integer>();
	private HashMap<String, Integer> locCount = new HashMap<String, Integer>();
	/* child 1: LOC by extension
	 * child 2: LOC by feature
	 * child 3: LOC by file
	 */
	private int childIndex;

	public HashMapNodeTwoStrings(String description, int childIndex, HashMap<String, Integer> extList) {
		super(description);
		extensionFeatureLOCList = extList;
		this.childIndex = childIndex;
	}

	@Override
	protected void initChildren() {
		for (String extAndFeature : extensionFeatureLOCList.keySet()) {
			String extensionName = extAndFeature.split("#")[0];
			String featureName = extAndFeature.split("#")[1];
//			System.out.println("## Start: "+ extAndFeature);//extAndFeature);
//			System.out.println("   ext:"+ extensionName);
//			System.out.println("   feat:"+ featureName);
			
			//LOC by extension
			if (childIndex == 1) {
				System.out.println("childIndex 1: ext");
				if (!locCount.containsKey(extensionName)) {
					locCount.put(extensionName, extensionFeatureLOCList.get(extAndFeature));
				} else {
					locCount.put(extensionName, locCount.get(extensionName) + extensionFeatureLOCList.get(extAndFeature));
				}
			//LOC by feature
			} else if (childIndex == 2) {
				System.out.println("childIndex 2: ext");
				if (!locCount.containsKey(featureName)) {
					locCount.put(featureName, extensionFeatureLOCList.get(extAndFeature));
				} else {
					locCount.put(featureName, locCount.get(featureName) + extensionFeatureLOCList.get(extAndFeature));
				}
			}
		}

		for (String key : locCount.keySet()) {
//			if (childIndex == 1) 
//			addChild(new HashMapNodeTwoStringsSub(name, locCount.get(name), extensionFeatureLOCList, false));
//			if (childIndex == 2)
//			addChild(new HashMapNodeTwoStringsSub(name, locCount.get(name), extensionFeatureLOCList, true));
			addChild(new HashMapNodeTwoStringsSub(key, locCount.get(key), extensionFeatureLOCList, childIndex));
		}

	}

}
