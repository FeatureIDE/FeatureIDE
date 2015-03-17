package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import java.util.LinkedList;

import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes.AbstractSortModeNode;

/**
 * Node to display the fields in the StatisticsProgrammSize
 * 
 * @author Schleicher Miro
 */
public class FieldNodeParent extends AbstractSortModeNode {

	private final FSTField fstField;

	public FieldNodeParent(String descString, FSTField fstField, LinkedList<FSTField> allFields) {
		super(descString);
		this.fstField = fstField;
		int numberOfRoles = countFieldsWithSameName(allFields);
		setValue(new Integer(numberOfRoles));
	}

	private int countFieldsWithSameName(LinkedList<FSTField> fields) {
		int c = 0;
		for (FSTField tempField : fields) {
			if (tempField.getFullIdentifier().equals(fstField.getFullIdentifier())) {
				c++;

				addChild(new FieldSubNodeParent(tempField.getRole().getFeature().getName(), tempField));
			}
		}
		return c;
	}

	@Override
	protected void initChildren() {
		
	}

}
