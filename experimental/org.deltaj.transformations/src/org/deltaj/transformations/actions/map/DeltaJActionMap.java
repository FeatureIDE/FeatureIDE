package org.deltaj.transformations.actions.map;

import java.util.Map;
import java.util.Set;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.transformations.actions.IDeltaJAction;
import org.deltaj.transformations.actions.finder.DeltaJActionFinder;
import org.deltaj.transformations.actions.targets.DeltaJActionTarget;
import org.deltaj.transformations.utils.MapFactory;
import org.deltaj.transformations.utils.SetFactory;
import org.deltaj.transformations.utils.exceptions.DeltaJException;

public class DeltaJActionMap {

	private final Map<DeltaJActionTarget, IDeltaJAction> actions;

	private DeltaJActionMap() {

		this.actions = MapFactory.createTreeMap();
	}

	public static DeltaJActionMap create(DeltaModule deltaModule) {

		DeltaJActionMap map = new DeltaJActionMap();

		for (IDeltaJAction deltaAction: new DeltaJActionFinder().find(deltaModule)) {

			map.add(deltaAction);
		}

		return map;
	}

	public Set<DeltaJActionTarget> getConflictingTargets(DeltaJActionMap other) {

		Set<DeltaJActionTarget> targets = SetFactory.createTreeSet(actions.keySet());
		targets.retainAll(other.actions.keySet());
		return targets;
	}

	public IDeltaJAction get(DeltaJActionTarget target) {

		return actions.get(target);
	}

	private void add(IDeltaJAction deltaAction) {

		DeltaJActionTarget actionTarget = new DeltaJActionTarget(deltaAction);

		if (actions.containsKey(actionTarget)) {
			throw new DeltaJException("Conflicting delta actions in a single delta module.");
		}

		actions.put(actionTarget, deltaAction);
	}
}
