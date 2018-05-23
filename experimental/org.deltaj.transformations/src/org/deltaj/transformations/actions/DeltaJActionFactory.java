package org.deltaj.transformations.actions;

import org.deltaj.deltaj.ClassAddition;
import org.deltaj.deltaj.Class;
import org.deltaj.deltaj.DeltaAction;
import org.deltaj.deltaj.Field;
import org.deltaj.deltaj.Method;
import org.deltaj.deltaj.DeltaSubAction;
import org.deltaj.transformations.utils.DeltaJHierarchy;

public class DeltaJActionFactory {

	public static IDeltaJClassAction get(DeltaAction actionStatement) {

		return new ClassAction(actionStatement);
	}

	public static IDeltaJAction get(DeltaSubAction subAction) {

		return new SubAction(subAction);
	}

	public static IDeltaJAction get(Method method) {

		Class parentClass = DeltaJHierarchy.getClassDefinition(method);
		ClassAddition addsClass = DeltaJHierarchy.getClassAddition(parentClass);
		return get(get(addsClass), method);
	}

	public static IDeltaJAction get(Field field) {

		Class parentClass = DeltaJHierarchy.getClassDefinition(field);
		ClassAddition addsClass = DeltaJHierarchy.getClassAddition(parentClass);
		return get(get(addsClass), field);
	}

	public static IDeltaJAction get(IDeltaJClassAction classAddition, Method methodStatement) {

		return new ImplicitMethodAddition(classAddition, methodStatement);
	}

	public static IDeltaJAction get(IDeltaJClassAction classAddition, Field fieldStatement) {

		return new ImplicitFieldAddition(classAddition, fieldStatement);
	}
}
