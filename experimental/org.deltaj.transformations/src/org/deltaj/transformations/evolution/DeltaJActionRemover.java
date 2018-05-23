package org.deltaj.transformations.evolution;

import org.deltaj.deltaj.ClassAddition;
import org.deltaj.deltaj.DeltaAction;
import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.DeltaSubAction;
import org.deltaj.transformations.actions.DeltaJActionFactory;
import org.deltaj.transformations.actions.DeltaJActionTargetType;
import org.deltaj.transformations.actions.IDeltaJAction;
import org.deltaj.transformations.actions.IDeltaJClassAction;
import org.deltaj.transformations.utils.DeltaJUnexpectedEnumValue;
import org.deltaj.transformations.utils.ListUtils;

public class DeltaJActionRemover {

	private final IDeltaJAction action;

	public DeltaJActionRemover(DeltaAction action) {

		this(DeltaJActionFactory.get(action));
	}

	public DeltaJActionRemover(DeltaSubAction action) {

		this(DeltaJActionFactory.get(action));
	}

	public DeltaJActionRemover(IDeltaJAction action) {

		this.action = action;
	}

	public void remove() {

		if (action.getTargetType() == DeltaJActionTargetType.CLASS) {
			ListUtils.removeElementByIdentity(action.getDeltaModule().getDeltaActions(), action.getActionStatement());
		} else {
			IDeltaJClassAction parentAction = action.getParentAction();
			switch (parentAction.getActionType()) {
			case ADDITION:
				ClassAddition addsClass = (ClassAddition) parentAction.getActionStatement();
				switch (action.getTargetType()) {
				case METHOD:
					ListUtils.removeElementByIdentity(addsClass.getClass_().getMethods(), action.getActionStatement());
					break;
				case FIELD:
					ListUtils.removeElementByIdentity(addsClass.getClass_().getFields(), action.getActionStatement());
					break;
				default:
					throw new DeltaJUnexpectedEnumValue();
				}
				break;
			case MODIFICATION:
				ClassModification modifiesClass = (ClassModification) parentAction.getActionStatement();
				ListUtils.removeElementByIdentity(modifiesClass.getSubActions(), action.getActionStatement());
				break;
			case REMOVAL:
				throw new DeltaJUnexpectedEnumValue();
			}
		}
	}
}
