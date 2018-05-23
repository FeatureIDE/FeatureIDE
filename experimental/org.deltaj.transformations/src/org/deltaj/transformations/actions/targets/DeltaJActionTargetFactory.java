package org.deltaj.transformations.actions.targets;

import org.deltaj.deltaj.Class;
import org.deltaj.deltaj.ClassAddition;
import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.ClassRemoval;
import org.deltaj.deltaj.Field;
import org.deltaj.deltaj.FieldAddition;
import org.deltaj.deltaj.FieldRemoval;
import org.deltaj.deltaj.Method;
import org.deltaj.deltaj.MethodAddition;
import org.deltaj.deltaj.MethodModification;
import org.deltaj.deltaj.MethodRemoval;
import org.deltaj.transformations.utils.DeltaJHierarchy;

public class DeltaJActionTargetFactory {

	public static DeltaJActionTarget create(ClassAddition classAddition) {

		Class classDefinition = classAddition.getClass_();
		return DeltaJActionTarget.createForClass(classDefinition.getName());
	}

	public static DeltaJActionTarget create(ClassRemoval classRemoval) {

		return DeltaJActionTarget.createForClass(classRemoval.getName());
	}

	public static DeltaJActionTarget create(Method methodDefinition) {

		Class classDefinition = DeltaJHierarchy.getClassDefinition(methodDefinition);
		return DeltaJActionTarget.createForMethod(classDefinition.getName(), methodDefinition.getName());
	}

	public static DeltaJActionTarget create(MethodAddition methodAddition) {

		Method method = methodAddition.getMethod();
		ClassModification classModification = DeltaJHierarchy.getClassModification(methodAddition);
		return DeltaJActionTarget.createForMethod(classModification.getName(), method.getName());
	}

	public static DeltaJActionTarget create(MethodModification methodModification) {

		Method method = methodModification.getMethod();
		ClassModification classModification = DeltaJHierarchy.getClassModification(methodModification);
		return DeltaJActionTarget.createForMethod(classModification.getName(), method.getName());
	}

	public static DeltaJActionTarget create(MethodRemoval methodRemoval) {

		ClassModification classModification = DeltaJHierarchy.getClassModification(methodRemoval);
		return DeltaJActionTarget.createForMethod(classModification.getName(), methodRemoval.getName());
	}

	public static DeltaJActionTarget create(Field fieldDefinition) {

		Class classDefinition = DeltaJHierarchy.getClassDefinition(fieldDefinition);
		return DeltaJActionTarget.createForField(classDefinition.getName(), fieldDefinition.getName());
	}

	public static DeltaJActionTarget create(FieldAddition fieldAddition) {

		Field field = fieldAddition.getField();
		ClassModification classModification = DeltaJHierarchy.getClassModification(fieldAddition);
		return DeltaJActionTarget.createForField(classModification.getName(), field.getName());
	}

	public static DeltaJActionTarget create(FieldRemoval fieldRemoval) {

		ClassModification classModification = DeltaJHierarchy.getClassModification(fieldRemoval);
		return DeltaJActionTarget.createForField(classModification.getName(), fieldRemoval.getName());
	}
}
