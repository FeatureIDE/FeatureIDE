package org.deltaj.transformations.utils.logical;

import org.deltaj.deltaj.ClassAddition;
import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.DeltaAction;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.transformations.utils.logical.actions.ILogicalAction;

public class LogicalActionsApplier {

	private final DeltaModule targetModule;
	private final DeltaModule sourceModule;

	public LogicalActionsApplier(DeltaModule targetModule, DeltaModule sourceModule) {

		this.targetModule = targetModule;
		this.sourceModule = sourceModule;
	}

	public void apply() {

		LogicalActionMap targetActions = new LogicalActionMapCreator(targetModule).create();
		LogicalActionMap sourceActions = new LogicalActionMapCreator(sourceModule).create();
		LogicalActionMap inverseActions = new LogicalActionMap();

		destroyStructure(targetModule);
		destroyStructure(sourceModule);

		for (ILogicalAction logicalAction: sourceActions.values()) {
			logicalAction.applyWithInverse(targetActions, inverseActions);
		}

		new DeltaModuleBuilder(targetModule, targetActions).build();
		new DeltaModuleBuilder(sourceModule, inverseActions).build();
	}

	private void destroyStructure(DeltaModule deltaModule) {

		for (DeltaAction deltaAction: deltaModule.getDeltaActions()) {

			if (deltaAction instanceof ClassAddition) {
				ClassAddition classAddition = (ClassAddition) deltaAction;
				classAddition.getClass_().getMethods().clear();
				classAddition.getClass_().getFields().clear();
			} else if (deltaAction instanceof ClassModification) {
				ClassModification classModification = (ClassModification) deltaAction;
				classModification.getSubActions().clear();
			}
		}

		deltaModule.getDeltaActions().clear();
	}
}
