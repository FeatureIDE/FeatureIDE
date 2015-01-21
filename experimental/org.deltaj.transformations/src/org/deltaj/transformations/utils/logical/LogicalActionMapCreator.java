package org.deltaj.transformations.utils.logical;

import org.deltaj.deltaj.ClassAddition;
import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.ClassRemoval;
import org.deltaj.deltaj.DeltaAction;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.DeltaSubAction;
import org.deltaj.deltaj.Field;
import org.deltaj.deltaj.FieldAddition;
import org.deltaj.deltaj.FieldRemoval;
import org.deltaj.deltaj.Method;
import org.deltaj.deltaj.MethodAddition;
import org.deltaj.deltaj.MethodModification;
import org.deltaj.deltaj.MethodRemoval;

public class LogicalActionMapCreator {

	private final DeltaModule deltaModule;
	private final LogicalActionMap actionMap;

	public LogicalActionMapCreator(DeltaModule deltaModule) {

		this.deltaModule = deltaModule;
		this.actionMap = new LogicalActionMap();
	}

	public LogicalActionMap create() {

		addLogicalActions();

		return actionMap;
	}

	private void addLogicalActions() {

		for (DeltaAction deltaAction: deltaModule.getDeltaActions()) {
			addDeltaAction(deltaAction);
		}
	}

	private void addDeltaAction(DeltaAction deltaAction) {

		if (deltaAction instanceof ClassAddition) {
			ClassAddition classAddition = (ClassAddition) deltaAction;
			addSubActions(classAddition);
			actionMap.addClassAddition(classAddition);
		} else if (deltaAction instanceof ClassModification) {
			ClassModification classModification = (ClassModification) deltaAction;
			addSubActions(classModification);
		} else if (deltaAction instanceof ClassRemoval) {
			actionMap.addClassRemoval((ClassRemoval) deltaAction);
		}
	}

	private void addSubActions(ClassAddition classAddition) {

		for (Field field: classAddition.getClass_().getFields()) {
			actionMap.addFieldAddition(field);
		}

		for (Method method: classAddition.getClass_().getMethods()) {
			actionMap.addMethodAddition(method);
		}
	}

	private void addSubActions(ClassModification classModification) {

		for (DeltaSubAction subAction: classModification.getSubActions()) {
			addSubAction(subAction);
		}
	}

	private void addSubAction(DeltaSubAction subAction) {

		if (subAction instanceof MethodAddition) {
			actionMap.addMethodAddition((MethodAddition) subAction);
		} else if (subAction instanceof MethodModification) {
			actionMap.addMethodModification((MethodModification) subAction);
		} else if (subAction instanceof MethodRemoval) {
			actionMap.addMethodRemoval((MethodRemoval) subAction);
		} else if (subAction instanceof FieldAddition) {
			actionMap.addFieldAddition((FieldAddition) subAction);
		} else if (subAction instanceof FieldRemoval) {
			actionMap.addFieldRemoval((FieldRemoval) subAction);
		}
	}
}
