package org.deltaj.transformations.merge.simple;

import java.util.List;
import java.util.Map;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.DeltaAction;
import org.deltaj.transformations.actions.DeltaJActionFactory;
import org.deltaj.transformations.actions.IDeltaJClassAction;
import org.deltaj.transformations.utils.MapFactory;
import org.deltaj.transformations.utils.MapUtils;

/**
 * Analyzes the class actions of a delta module and merges them if possible.
 * 
 * @author Oliver Richers
 */
public class DeltaJClassActionsOfModuleMerger {

	private final DeltaModule deltaModule;

	public DeltaJClassActionsOfModuleMerger(DeltaModule deltaModule) {

		this.deltaModule = deltaModule;
	}

	public void merge() {

		Map<String, List<IDeltaJClassAction>> actionMap = collectClassActions();

		mergeActions(actionMap);
	}

	private Map<String, List<IDeltaJClassAction>> collectClassActions() {

		Map<String, List<IDeltaJClassAction>> actionMap = MapFactory.createTreeMap();

		for (DeltaAction actionStatement: deltaModule.getDeltaActions()) {

			IDeltaJClassAction classAction = DeltaJActionFactory.get(actionStatement);
			MapUtils.addToListMap(actionMap, classAction.getTargetName(), classAction);
		}

		return actionMap;
	}

	private void mergeActions(Map<String, List<IDeltaJClassAction>> actionMap) {

		for (List<IDeltaJClassAction> classAction: actionMap.values()) {

			if (classAction.size() > 1) {
				merge(classAction);
			}
		}
	}

	private void merge(List<IDeltaJClassAction> classActions) {

		new DeltaJClassActionMerger(classActions).merge();
	}
}
