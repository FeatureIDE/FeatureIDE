package org.deltaj.transformations.inverse;

import org.deltaj.deltaj.ClassAddition;
import org.deltaj.deltaj.DeltaAction;
import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.ClassModification;
import org.eclipse.xtext.util.PolymorphicDispatcher;

/**
 * This class dispatches the building of inverses of {@link DeltaAction}
 * statements to the actual builder classes.
 * 
 * @author Oliver Richers
 */
class InverseActionBuilderDispatcher {

	private final DeltajFactory factory;
	private final PolymorphicDispatcher<DeltaAction> dispatcher;

	public InverseActionBuilderDispatcher(DeltajFactory factory) {

		this.factory = factory;
		this.dispatcher = PolymorphicDispatcher.createForSingleTarget("build", 1, 1, this);
	}

	public DeltaAction dispatch(DeltaAction deltaAction) {

		return dispatcher.invoke(deltaAction);
	}

	protected DeltaAction build(ClassAddition addsClassStatement) {

		return new InverseAddsClassBuilder(factory, addsClassStatement).build();
	}

	protected DeltaAction build(ClassModification modifiesClassStatement) {

		return new InverseModifiesClassBuilder(factory, modifiesClassStatement).build();
	}
}
