
package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes;

import java.util.HashMap;

import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * TODO description
 * 
 * @author Schleicher Miro
 */
public class HashMapNodeTwoStringsSub extends AbstractSortModeNode {

	
	HashMap<String, Integer> featureExtensionLOCList;
	HashMap<String, Integer> count;
	String name;
	int side;
	
	public HashMapNodeTwoStringsSub(String name, Integer integer, HashMap<String, Integer> featureExtensionLOCList, int side) {
		super(name, integer);
		this.featureExtensionLOCList = featureExtensionLOCList;
		count = new HashMap<String, Integer>();
		this.name = name;
		this.side = side;
	}

	@Override
	protected void initChildren() {
		
		for (String tempName : featureExtensionLOCList.keySet()) {
			if(side == 1 && tempName.split("#")[0].equals(name)) {
				if(!count.containsKey(tempName.split("#")[1])) {
					count.put(tempName.split("#")[1], featureExtensionLOCList.get(tempName) );
				} else {
					count.put(tempName.split("#")[1], count.get(tempName.split("#")[1]) + featureExtensionLOCList.get(tempName) );
				}
			} else if(side == 2 && tempName.split("#")[1].equals(name)) {
				if(!count.containsKey(tempName.split("#")[0])) {
					count.put(tempName.split("#")[0], featureExtensionLOCList.get(tempName) );
				} else {
					count.put(tempName.split("#")[0], count.get(tempName.split("#")[0]) + featureExtensionLOCList.get(tempName) );
				}
			}
		}
		
		for (String key : count.keySet()) {
			addChild(new Parent(key, count.get(key)));
		}
		
	}
	
}
