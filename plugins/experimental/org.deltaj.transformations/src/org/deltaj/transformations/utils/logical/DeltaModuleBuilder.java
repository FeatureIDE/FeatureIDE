package org.deltaj.transformations.utils.logical;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.deltaj.deltaj.Class;
import org.deltaj.deltaj.ClassAddition;
import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.ClassRemoval;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.transformations.actions.targets.DeltaJActionTarget;
import org.deltaj.transformations.utils.ListFactory;
import org.deltaj.transformations.utils.MapFactory;
import org.deltaj.transformations.utils.SetFactory;
import org.deltaj.transformations.utils.exceptions.DeltaJException;
import org.deltaj.transformations.utils.logical.actions.ILogicalAction;
import org.deltaj.transformations.utils.logical.actions.ILogicalClassAction;
import org.deltaj.transformations.utils.logical.actions.ILogicalSubAction;
import org.deltaj.transformations.utils.logical.actions.ILogicalSubAddition;
import org.deltaj.transformations.utils.logical.actions.ILogicalSubRemoval;
import org.deltaj.transformations.utils.logical.actions.LogicalClassAddition;
import org.deltaj.transformations.utils.logical.actions.LogicalClassRemoval;

public class DeltaModuleBuilder {

	private final DeltajFactory factory;
	private final DeltaModule deltaModule;
	private final LogicalActionMap logicalActions;
	private final Map<DeltaJActionTarget, ClassAddition> classAdditions;
	private final Map<DeltaJActionTarget, ClassModification> classModifications;
	private final Set<DeltaJActionTarget> removedClasses;

	public DeltaModuleBuilder(DeltaModule deltaModule, LogicalActionMap logicalActions) {

		this.factory = DeltajFactory.eINSTANCE;
		this.deltaModule = deltaModule;
		this.logicalActions = logicalActions;
		this.classAdditions = MapFactory.createTreeMap();
		this.classModifications = MapFactory.createTreeMap();
		this.removedClasses = SetFactory.createTreeSet();
	}

	public void build() {

		collectRemovedClasses();

		addClassAdditions();
		addSubActions();
		addClassModifications();
		addClassRemovals();
	}

	private void collectRemovedClasses() {

		for (ILogicalAction logicalAction: logicalActions.values()) {
			if (logicalAction instanceof LogicalClassRemoval) {
				removedClasses.add(logicalAction.getTarget());
			}
		}
	}

	private void addClassAdditions() {

		for (ILogicalAction logicalAction: logicalActions.values()) {
			if (logicalAction instanceof LogicalClassAddition) {
				addClassAddition((LogicalClassAddition) logicalAction);
			}
		}
	}

	private void addClassAddition(LogicalClassAddition logicalAddition) {

		// get class definition
		Class classDefinition = logicalAddition.getClassDefinition();

		// build syntactical addition
		ClassAddition classAddition = factory.createClassAddition();
		classAddition.setClass(classDefinition);
		deltaModule.getDeltaActions().add(classAddition);

		// put into map
		classAdditions.put(logicalAddition.getTarget(), classAddition);
	}

	private void addSubActions() {

		for (ILogicalAction logicalAction: getActionsSorted()) {
			if (logicalAction instanceof ILogicalSubAddition) {
				addSubAddition((ILogicalSubAddition) logicalAction);
			} else if (logicalAction instanceof ILogicalSubRemoval) {
				addSubRemoval((ILogicalSubRemoval) logicalAction);
			} else if (logicalAction instanceof ILogicalSubAction) {
				addSubAction((ILogicalSubAction) logicalAction);
			} else if (logicalAction instanceof ILogicalClassAction) {
				// nothing to do
			} else {
				throw new DeltaJException("Invalid logical action.");
			}
		}
	}

	private List<ILogicalAction> getActionsSorted() {

		List<ILogicalAction> actionList = ListFactory.createArrayList(logicalActions.values());
		Collections.sort(actionList, new LogicalActionComparator());
		return actionList;
	}

	private void addSubAddition(ILogicalSubAddition subAddition) {

//		System.out.printf("adding sub addition for '%s'\n", subAddition.getFullTargetName());

		DeltaJActionTarget classTarget = subAddition.getTarget().getClassTarget();
		ClassAddition classAddition = classAdditions.get(classTarget);
		if (classAddition != null) {
			subAddition.addTo(classAddition);
		} else {
//			System.out.printf("no class addition for '%s' found\n", classTarget.getFullName());
			subAddition.addTo(getClassModification(classTarget));
		}
	}

	private void addSubRemoval(ILogicalSubRemoval subRemoval) {

		DeltaJActionTarget classTarget = subRemoval.getTarget().getClassTarget();
		if (!removedClasses.contains(classTarget)) {
			addSubAction(subRemoval);
		}
	}

	private void addSubAction(ILogicalSubAction subAction) {

		DeltaJActionTarget classTarget = subAction.getTarget().getClassTarget();
		subAction.addTo(getClassModification(classTarget));
	}

	private ClassModification getClassModification(DeltaJActionTarget classTarget) {

		ClassModification classModification = classModifications.get(classTarget);

		if (classModification == null) {
			classModification = factory.createClassModification();
			classModification.setName(classTarget.getClassName());
			classModifications.put(classTarget, classModification);
		}

		return classModification;
	}

	private void addClassModifications() {

		for (ClassModification classModification: classModifications.values()) {
			if (!classModification.getSubActions().isEmpty()) {
				deltaModule.getDeltaActions().add(classModification);
			}
		}
	}

	private void addClassRemovals() {

		for (ILogicalAction logicalAction: logicalActions.values()) {
			if (logicalAction instanceof LogicalClassRemoval) {
				addClassRemoval((LogicalClassRemoval) logicalAction);
			}
		}
	}

	private void addClassRemoval(LogicalClassRemoval logicalRemoval) {

		ClassRemoval classRemoval = factory.createClassRemoval();
		classRemoval.setName(logicalRemoval.getTarget().getClassName());
		deltaModule.getDeltaActions().add(classRemoval);
	}
}
