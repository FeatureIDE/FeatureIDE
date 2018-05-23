package org.deltaj.transformations.extract;

import java.util.Set;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.transformations.actions.DeltaJActionTargetType;
import org.deltaj.transformations.actions.DeltaJActionType;
import org.deltaj.transformations.actions.IDeltaJAction;
import org.deltaj.transformations.actions.map.DeltaJActionMap;
import org.deltaj.transformations.actions.targets.DeltaJActionTarget;

public class DeltaJConflictingActionsExtractor {

	private final DeltaJActionMap actionMapA;
	private final DeltaJActionMap actionMapB;

	public DeltaJConflictingActionsExtractor(DeltaModule deltaModuleA, DeltaModule deltaModuleB) {

		this.actionMapA = DeltaJActionMap.create(deltaModuleA);
		this.actionMapB = DeltaJActionMap.create(deltaModuleB);
	}

	public void extract() {

		extract(actionMapA.getConflictingTargets(actionMapB));
	}

	private void extract(Set<DeltaJActionTarget> conflictingTargets) {

		for (DeltaJActionTarget conflictingTarget: conflictingTargets) {

			IDeltaJAction actionA = actionMapA.get(conflictingTarget);
			IDeltaJAction actionB = actionMapB.get(conflictingTarget);

			if (isClassModification(actionA) || isClassModification(actionB)) {
				continue;
			}

			new DeltaJActionExtractor(actionA).extractIfNecessary();
			new DeltaJActionExtractor(actionB).extractIfNecessary();
		}
	}

	private boolean isClassModification(IDeltaJAction action) {

		return action.getTargetType() == DeltaJActionTargetType.CLASS
				&& action.getActionType() == DeltaJActionType.MODIFICATION;
	}
}
