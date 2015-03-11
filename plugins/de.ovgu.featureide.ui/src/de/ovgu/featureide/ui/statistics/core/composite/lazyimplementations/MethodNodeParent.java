package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import java.util.LinkedList;

import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * TODO description
 * 
 * @author Schleicher Miro
 */
public class MethodNodeParent extends LazyParent {

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.statistics.core.composite.LazyParent#initChildren()
	 */
	FSTMethod fstMethod;
	
	
	public MethodNodeParent(String descString, FSTMethod fstMethod, LinkedList<FSTMethod> allMethods){
		
		super(descString);
		this.fstMethod = fstMethod;
		int numberOfRoles = countMethodsWithSameName(allMethods);
		setValue(new Integer(numberOfRoles));
		
	}
	

	private int countMethodsWithSameName(LinkedList<FSTMethod> methods) {
		int c = 0;
		for (FSTMethod tempMethod : methods) {
			if(tempMethod.getFullIdentifier().equals(fstMethod.getFullIdentifier())) {
				c++;
				
				addChild(new Parent(tempMethod.getRole().getFeature().getName(), tempMethod));
			}
		}
		return c;
	}

	@Override
	protected void initChildren() {
		
	}

}
