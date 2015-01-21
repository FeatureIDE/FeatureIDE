package org.deltaj.transformations.merge;

import java.util.List;
import org.deltaj.deltaj.DeltaAction;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.transformations.evolution.DeltaJModuleRemover;
import org.deltaj.transformations.utils.ListFactory;

/**
 * Merges one delta module into another delta module.
 * <p>
 * This moves the actions from the second delta module into the first delta
 * module and then removes the second delta module.
 * <p>
 * This transformation assumes that both delta modules have equivalent
 * application conditions and are part of the same partition part.
 * 
 * @author Oliver Richers
 */
public class DeltaJModulesWithEquivalentConditionsMerger {

	private final DeltaModule deltaModuleA;
	private final DeltaModule deltaModuleB;

	public DeltaJModulesWithEquivalentConditionsMerger(DeltaModule deltaModuleA, DeltaModule deltaModuleB) {

		this.deltaModuleA = deltaModuleA;
		this.deltaModuleB = deltaModuleB;
	}

	public void merge() {

		moveActions();
		removeSecondDeltaModule();
	}

	private void removeSecondDeltaModule() {

		new DeltaJModuleRemover(deltaModuleB).remove();
	}

	private void moveActions() {

		// copying list to avoid site-effects
		List<DeltaAction> deltaActions = ListFactory.createArrayList(deltaModuleB.getDeltaActions());

		for (DeltaAction deltaAction: deltaActions) {
			deltaModuleA.getDeltaActions().add(deltaAction);
		}
	}
}
