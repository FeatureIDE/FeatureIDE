package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import java.util.LinkedList;

import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * TODO description
 * 
 * @author Schleicher Miro
 */
public class FieldNodeParent extends LazyParent {

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.statistics.core.composite.LazyParent#initChildren()
	 */
	FSTField fstField;
	
	
	public FieldNodeParent(String descString, FSTField fstField, LinkedList<FSTField> allFields){
		
		super(descString);
		this.fstField = fstField;
		int numberOfRoles = countFieldsWithSameName(allFields);
		setValue(new Integer(numberOfRoles));
		
	}
	

	private int countFieldsWithSameName(LinkedList<FSTField> fields) {
		int c = 0;
		for (FSTField tempField : fields) {
			if(tempField.getFullIdentifier().equals(fstField.getFullIdentifier())) {
				c++;
				
				addChild(new Parent(tempField.getRole().getFeature().getName(), tempField));
			}
		}
		return c;
	}

	@Override
	protected void initChildren() {
		
	}

}
