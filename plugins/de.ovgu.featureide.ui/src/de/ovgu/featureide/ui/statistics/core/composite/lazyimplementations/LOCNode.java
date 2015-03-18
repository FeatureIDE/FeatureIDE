package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import java.util.HashMap;

import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes.HashMapNode;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes.HashMapNodeTwoStrings;

/**
 * TODO description
 * 
 * @author Schleicher Miro
 */
public class LOCNode extends LazyParent {
	
	HashMap<String, Integer> featureExtensionLOCList = new HashMap<String, Integer>();
	
	LOCNode(String description, HashMap<String, Integer> fExList){
		super(description);
		featureExtensionLOCList = fExList;
	}
	
	@Override
	protected void initChildren() {

		
		
		addChild(new HashMapNodeTwoStrings("LOC by extension", 1, featureExtensionLOCList));
		addChild(new HashMapNodeTwoStrings("LOC by feature", 2, featureExtensionLOCList));
		
	}

}
