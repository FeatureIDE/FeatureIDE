package org.deltaj.transformations.extract;

import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.FieldAddition;
import org.deltaj.deltaj.MethodAddition;
import org.deltaj.deltaj.DeltaSubAction;
import org.deltaj.transformations.actions.IDeltaJAction;
import org.deltaj.transformations.actions.IDeltaJClassAction;
import org.deltaj.transformations.actions.IDeltaJClassSubAction;
import org.deltaj.transformations.actions.IDeltaJImplicitFieldAddition;
import org.deltaj.transformations.actions.IDeltaJImplicitMethodAddition;
import org.eclipse.xtext.util.PolymorphicDispatcher;

class ActionMover {

	private final DeltajFactory factory;
	private final DeltaModule deltaModule;
	private final PolymorphicDispatcher<Void> dispatcher;

	public ActionMover(DeltaModule deltaModule) {

		this.factory = DeltajFactory.eINSTANCE;
		this.deltaModule = deltaModule;
		this.dispatcher = PolymorphicDispatcher.createForSingleTarget("moveAction", 1, 1, this);
	}

	public void move(IDeltaJAction action) {

		dispatcher.invoke(action);
	}

	protected void moveAction(IDeltaJClassAction action) {

		deltaModule.getDeltaActions().add(action.getActionStatement());
	}

	protected void moveAction(IDeltaJClassSubAction action) {

		moveAction(action.getParentAction(), action.getActionStatement());
	}

	protected void moveAction(IDeltaJImplicitMethodAddition action) {

		MethodAddition addition = factory.createMethodAddition();
		addition.setMethod(action.getActionStatement());

		moveAction(action.getParentAction(), addition);
	}

	protected void moveAction(IDeltaJImplicitFieldAddition action) {

		FieldAddition addition = factory.createFieldAddition();
		addition.setField(action.getActionStatement());

		moveAction(action.getParentAction(), addition);
	}

	private void moveAction(IDeltaJClassAction classAction, DeltaSubAction action) {

		ClassModification modification = factory.createClassModification();
		modification.setName(classAction.getTargetName());
		modification.getSubActions().add(action);

		deltaModule.getDeltaActions().add(modification);
	}
}
