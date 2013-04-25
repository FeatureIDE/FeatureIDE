package org.deltaj.transformations.utils.logical;

import java.util.Collection;
import java.util.Map;
import org.deltaj.deltaj.ClassAddition;
import org.deltaj.deltaj.ClassRemoval;
import org.deltaj.deltaj.Field;
import org.deltaj.deltaj.FieldAddition;
import org.deltaj.deltaj.FieldRemoval;
import org.deltaj.deltaj.Method;
import org.deltaj.deltaj.MethodAddition;
import org.deltaj.deltaj.MethodModification;
import org.deltaj.deltaj.MethodRemoval;
import org.deltaj.transformations.actions.targets.DeltaJActionTarget;
import org.deltaj.transformations.utils.MapFactory;
import org.deltaj.transformations.utils.logical.actions.ILogicalAction;
import org.deltaj.transformations.utils.logical.actions.LogicalClassAddition;
import org.deltaj.transformations.utils.logical.actions.LogicalClassRemoval;
import org.deltaj.transformations.utils.logical.actions.LogicalFieldAddition;
import org.deltaj.transformations.utils.logical.actions.LogicalFieldRemoval;
import org.deltaj.transformations.utils.logical.actions.LogicalMethodAddition;
import org.deltaj.transformations.utils.logical.actions.LogicalMethodModification;
import org.deltaj.transformations.utils.logical.actions.LogicalMethodRemoval;

public class LogicalActionMap {

	private final Map<DeltaJActionTarget, ILogicalAction> actions;

	public LogicalActionMap() {

		this.actions = MapFactory.createTreeMap();
	}

	public ILogicalAction get(DeltaJActionTarget actionTarget) {

		return actions.get(actionTarget);
	}

	public Collection<ILogicalAction> values() {

		return actions.values();
	}

	public void remove(DeltaJActionTarget target) {

		actions.remove(target);
	}

	public void addClassAddition(ClassAddition classAddition) {

		add(new LogicalClassAddition(classAddition));
	}

	public void addClassRemoval(ClassRemoval classRemoval) {

		add(new LogicalClassRemoval(classRemoval));
	}

	public void addMethodAddition(Method method) {

		add(new LogicalMethodAddition(method));
	}

	public void addMethodAddition(MethodAddition methodAddition) {

		add(new LogicalMethodAddition(methodAddition));
	}

	public void addMethodModification(MethodModification methodModification) {

		add(new LogicalMethodModification(methodModification));
	}

	public void addMethodRemoval(MethodRemoval methodRemoval) {

		add(new LogicalMethodRemoval(methodRemoval));
	}

	public void addFieldAddition(Field field) {

		add(new LogicalFieldAddition(field));
	}

	public void addFieldAddition(FieldAddition fieldAddition) {

		add(new LogicalFieldAddition(fieldAddition));
	}

	public void addFieldRemoval(FieldRemoval fieldRemoval) {

		add(new LogicalFieldRemoval(fieldRemoval));
	}

	public void add(ILogicalAction deltaAction) {

		actions.put(deltaAction.getTarget(), deltaAction);
	}
}
