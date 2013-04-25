package org.deltaj.transformations.exceptions;

import org.deltaj.deltaj.DeltaAction;
import org.deltaj.deltaj.DeltaSubAction;
import org.deltaj.transformations.utils.exceptions.DeltaJException;

public class DeltaJInvalidActionType extends DeltaJException {

	public DeltaJInvalidActionType(DeltaAction actionStatement) {

		this(actionStatement.getClass());
	}

	public DeltaJInvalidActionType(DeltaSubAction actionStatement) {

		this(actionStatement.getClass());
	}

	public DeltaJInvalidActionType(Class<?> actionClass) {

		super("Invalid delta action type: " + actionClass.getName());
	}
}
