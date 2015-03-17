package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import java.util.HashMap;

import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes.HashMapNode;

/**
 * TODO description
 * 
 * @author Schleicher Miro
 */
public class LOCNode extends LazyParent {
	
	HashMap<String, Integer> extensionLOCList = new HashMap<String, Integer>();
	HashMap<String, Integer> featureLOCList = new HashMap<String, Integer>();
	
	LOCNode(String description, HashMap<String, Integer> extensionList, HashMap<String, Integer> featureList){
		super(description);
		extensionLOCList = extensionList;
		featureLOCList = featureList;
	}
	
	@Override
	protected void initChildren() {

		addChild(new HashMapNode("LOC sorted by extensions", null, extensionLOCList));
		addChild(new HashMapNode("LOC sorted by feature", null, featureLOCList));
		
	}

}
