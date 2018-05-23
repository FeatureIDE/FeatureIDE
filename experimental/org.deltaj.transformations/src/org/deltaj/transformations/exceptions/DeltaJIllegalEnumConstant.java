package org.deltaj.transformations.exceptions;

import org.deltaj.transformations.utils.exceptions.DeltaJException;

public class DeltaJIllegalEnumConstant extends DeltaJException {

	public DeltaJIllegalEnumConstant(Enum<?> enumConstant) {

		super("Invalid enum constant '%s' of enum class '%s'.", enumConstant.name(), enumConstant.getClass().getName());
	}
}
