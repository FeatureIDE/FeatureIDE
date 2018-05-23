package org.deltaj.transformations.inverse;

import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.DeltaSubAction;

/**
 * This class builds the inverse of an {@link ClassModification} statement.
 * 
 * @author Oliver Richers
 */
class InverseModifiesClassBuilder {

	private final DeltajFactory factory;
	private final ClassModification modifiesClassStatement;

	public InverseModifiesClassBuilder(DeltajFactory factory, ClassModification modifiesClassStatement) {

		this.factory = factory;
		this.modifiesClassStatement = modifiesClassStatement;
	}

	public ClassModification build() {

		ClassModification inverseAction = factory.createClassModification();

		inverseAction.setName(modifiesClassStatement.getName());

		for (DeltaSubAction classAction: modifiesClassStatement.getSubActions()) {

			DeltaSubAction inverseClassAction = new InverseClassActionBuilderDispatcher(factory)
					.dispatch(classAction);

			inverseAction.getSubActions().add(inverseClassAction);
		}

		return inverseAction;
	}
}
