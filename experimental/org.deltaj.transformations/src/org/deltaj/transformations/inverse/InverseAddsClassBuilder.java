package org.deltaj.transformations.inverse;

import org.deltaj.deltaj.ClassAddition;
import org.deltaj.deltaj.ClassRemoval;
import org.deltaj.deltaj.DeltajFactory;

/**
 * This class builds the inverse of an {@link ClassAddition} statement.
 * 
 * @author Oliver Richers
 */
class InverseAddsClassBuilder {

	private final DeltajFactory factory;
	private final ClassAddition addsClassStatement;

	public InverseAddsClassBuilder(DeltajFactory factory, ClassAddition addsClassStatement) {

		this.factory = factory;
		this.addsClassStatement = addsClassStatement;
	}

	public ClassRemoval build() {

		ClassRemoval inverseAction = factory.createClassRemoval();

		inverseAction.setName(addsClassStatement.getClass_().getName());

		return inverseAction;
	}
}
