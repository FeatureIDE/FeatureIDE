package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * TODO description
 * 
 * @author Schleicher Miro
 */
public class FieldSubNodeParent extends Parent {

	FSTField field;

	public FieldSubNodeParent(String descString, FSTField field) {
		super(descString.replace(":", ""));
		this.field = field;
	}

	public FSTField getField() {
		return field;
	}

}