package org.deltaj.transformations.inverse;

import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.MethodAddition;
import org.deltaj.deltaj.MethodRemoval;

/**
 * This class builds the inverse of an {@link MethodAddition} statement.
 * 
 * @author Oliver Richers
 */
class InverseAddsMethodBuilder {

	private final DeltajFactory factory;
	private final MethodAddition addsMethod;

	public InverseAddsMethodBuilder(DeltajFactory factory, MethodAddition addsMethod) {

		this.factory = factory;
		this.addsMethod = addsMethod;
	}

	public MethodRemoval build() {

		MethodRemoval inverseAction = factory.createMethodRemoval();

		inverseAction.setName(addsMethod.getMethod().getName());

		return inverseAction;
	}
}
