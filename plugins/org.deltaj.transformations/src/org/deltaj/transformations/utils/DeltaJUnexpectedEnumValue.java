package org.deltaj.transformations.utils;

import org.deltaj.transformations.utils.exceptions.DeltaJException;

public class DeltaJUnexpectedEnumValue extends DeltaJException {

	public DeltaJUnexpectedEnumValue() {

		super("Unexpected enum value encountered.");
	}
}
