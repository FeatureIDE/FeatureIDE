package org.deltaj.transformations.actions.finder;

import org.deltaj.transformations.actions.IDeltaJAction;
import org.deltaj.transformations.modules.references.DeltaJModuleReference;

/**
 * Searches through the product line to find all actions preceding the specified
 * action, and affecting the same class.
 * 
 * @author Oliver Richers
 */
public class DeltaJPrecedingActionFinder extends DeltaJActionByTargetFinder {

	private final DeltaJModuleReference moduleReference;
	private final String splName;

	public DeltaJPrecedingActionFinder(IDeltaJAction referenceAction, DeltaJModuleReference moduleReference) {

		super(referenceAction.getTargetName());

		this.moduleReference = moduleReference;
		this.splName = moduleReference.getSplName();
	}

	@Override
	protected boolean matches(IDeltaJAction action) {

		return super.matches(action) && isBeforeReferenceAction(action);

	}

	private boolean isBeforeReferenceAction(IDeltaJAction action) {

		DeltaJModuleReference actionReference = action.findModuleReferences().get(splName);

		if (actionReference == null) {
			return false; // not used in the same product line
		}

		return actionReference.getPartitionOrder() < moduleReference.getPartitionOrder();
	}
}
