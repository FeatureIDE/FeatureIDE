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

import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * Node in the statistics view to show lines of code.<br>
 * Creates each entry for the category loc by feature or
 * loc by extension.
 * 
 * @author Schleicher Miro
 * @author Maximilian Homann
 * @author Philipp Kuhn
 */
public class HashMapNodeTwoStringsSub extends HashMapNodeTwoStrings {

	private String selectedParent;
	
	public HashMapNodeTwoStringsSub(String selectedParent, Integer locCount, int childIndex, HashMap<String, Integer> featureExtensionLOCList, HashMap<String, Integer> extensionFileLOCList) {
		super(selectedParent, locCount, childIndex, featureExtensionLOCList, extensionFileLOCList);
		this.selectedParent = selectedParent;
		
	}

	//team2
	@Override
	protected void initChildren() {
		for (String extAndFeature : extensionFeatureLOCList.keySet()) {
			String extensionName = extAndFeature.split("#")[0];
			String featureName = extAndFeature.split("#")[1];
		
			//LOC by Extension
			if(childIndex == 1 && extensionName.equals(selectedParent)) {
				if(!locCount.containsKey(featureName)) {
					locCount.put(featureName, extensionFeatureLOCList.get(extAndFeature));
				} else {
					locCount.put(featureName, locCount.get(featureName) + extensionFeatureLOCList.get(extAndFeature));
				}
			//LOC by Feature
			} else if(childIndex == 2 && featureName.equals(selectedParent)) {
					if(!locCount.containsKey(extensionName)) {
						locCount.put(extensionName, extensionFeatureLOCList.get(extAndFeature));
					} else {
						locCount.put(extensionName, locCount.get(extensionName) + extensionFeatureLOCList.get(extAndFeature));
					}
			} 
		}
		
		for (String extAndFile: extensionFileLOCList.keySet()) {
			String fileName = extAndFile.split("#")[1];
			String extensionName = extAndFile.split("#")[0];
			//LOC by file
			if(childIndex == 3 && extensionName.equals(selectedParent)){
				if (!locCount.containsKey(fileName)) {
					locCount.put(fileName, extensionFileLOCList.get(extAndFile));
				}
			}
		}
		
		for (String key : locCount.keySet()) {
			addChild(new Parent(key, locCount.get(key)));
		}
	}
	
}
