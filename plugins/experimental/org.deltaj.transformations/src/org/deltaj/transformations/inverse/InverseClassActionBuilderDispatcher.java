package org.deltaj.transformations.inverse;

import org.deltaj.deltaj.MethodAddition;
import org.deltaj.deltaj.DeltaAction;
import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.DeltaSubAction;
import org.deltaj.transformations.utils.visitor.VisitorDispatcher;
import org.eclipse.xtext.util.PolymorphicDispatcher;

/**
 * This class dispatches the building of inverses of {@link DeltaSubAction}
 * statements to the actual builder classes.
 * 
 * @author Oliver Richers
 */
class InverseClassActionBuilderDispatcher extends VisitorDispatcher<DeltaAction> {

	private final DeltajFactory factory;
	private final PolymorphicDispatcher<DeltaSubAction> dispatcher;

	public InverseClassActionBuilderDispatcher(DeltajFactory factory) {

		this.factory = factory;
		this.dispatcher = PolymorphicDispatcher.createForSingleTarget("build", 1, 1, this);
	}

	public DeltaSubAction dispatch(DeltaSubAction classAction) {

		return dispatcher.invoke(classAction);
	}

	protected DeltaSubAction build(MethodAddition addsMethod) {

		return new InverseAddsMethodBuilder(factory, addsMethod).build();
	}
}
