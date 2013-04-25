package org.deltaj.transformations.actions.targets;

import org.deltaj.transformations.actions.DeltaJActionTargetType;
import org.deltaj.transformations.actions.IDeltaJAction;
import org.deltaj.transformations.utils.exceptions.DeltaJException;

public class DeltaJActionTarget implements Comparable<DeltaJActionTarget> {

	private final DeltaJActionTargetType targetType;
	private final String className;
	private final String subName;

	private DeltaJActionTarget(DeltaJActionTargetType targetType, String className, String subName) {

		this.targetType = targetType;
		this.className = className;
		this.subName = subName;
	}

	public DeltaJActionTarget(IDeltaJAction action) {

		String[] nameParts = action.getTargetName().split("\\.");

		this.targetType = action.getTargetType();
		this.className = nameParts[0];
		this.subName = nameParts.length > 1? nameParts[1] : "";
	}

	public static DeltaJActionTarget createForClass(String className) {

		return new DeltaJActionTarget(DeltaJActionTargetType.CLASS, className, "");
	}

	public static DeltaJActionTarget createForMethod(String className, String methodName) {

		return new DeltaJActionTarget(DeltaJActionTargetType.METHOD, className, methodName);
	}

	public static DeltaJActionTarget createForField(String className, String fieldName) {

		return new DeltaJActionTarget(DeltaJActionTargetType.FIELD, className, fieldName);
	}

	public DeltaJActionTargetType getTargetType() {

		return targetType;
	}

	public String getClassName() {

		return className;
	}

	public String getSubName() {

		return subName;
	}

	public String getFullName() {

		return subName.isEmpty()? className : className + "." + subName;
	}

	public DeltaJActionTarget getClassTarget() {

		if (targetType == DeltaJActionTargetType.CLASS) {
			throw new DeltaJException("Cannot get class target of a class.");
		}

		return new DeltaJActionTarget(DeltaJActionTargetType.CLASS, className, "");
	}

	@Override
	public int compareTo(DeltaJActionTarget other) {

		return DeltaJActionTargetComparator.get().compare(this, other);
	}
}
