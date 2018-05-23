package org.deltaj.transformations.resolve;

import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.Method;
import org.deltaj.deltaj.MethodAddition;
import org.deltaj.deltaj.MethodModification;
import org.deltaj.transformations.actions.DeltaJActionFactory;
import org.deltaj.transformations.actions.IDeltaJAction;
import org.deltaj.transformations.utils.ListUtils;
import org.deltaj.transformations.utils.exceptions.DeltaJException;
import org.eclipse.emf.ecore.EObject;

/**
 * Resolves the specified method modification action.
 * <p>
 * Every method modification action can converted into a method addition action
 * by disabling all preceding delta actions affecting the same target for those
 * cases where the application condition of the modification action would
 * evaluate to true.
 * 
 * @author Oliver Richers
 */
public class DeltaJModificationActionResolver {

	private final IDeltaJAction modificationAction;
	private final MethodModification modificationStatement;

	public DeltaJModificationActionResolver(MethodModification modificationAction) {

		this(DeltaJActionFactory.get(modificationAction));
	}

	public DeltaJModificationActionResolver(IDeltaJAction modificationAction) {

		this.modificationAction = modificationAction;
		this.modificationStatement = getModificationStatement();
	}

	private MethodModification getModificationStatement() {

		EObject statement = modificationAction.getActionStatement();

		if (statement instanceof MethodModification) {
			return (MethodModification) statement;
		} else {
			throw new DeltaJException("The specified action is not a method modification action: %s", statement
					.getClass()
					.getCanonicalName());
		}
	}

	public void resolve() {

		disablePrecedingActions();

		convertModificationAction();
	}

	private void disablePrecedingActions() {

		new PrecedingActionsDisabler(modificationAction).disable();
	}

	private void convertModificationAction() {

		// create new addition statement
		Method method = modificationStatement.getMethod();
		MethodAddition additionStatement = DeltajFactory.eINSTANCE.createMethodAddition();
		additionStatement.setMethod(method);

		// replace modification with addition statement
		ClassModification modifiesClass = (ClassModification) modificationStatement.eContainer();
		ListUtils.replaceElementByIdentity(modifiesClass.getSubActions(), modificationStatement, additionStatement);
//		int index = ListUtils.findElementByIdentity(modifiesClass.getActions(), modificationStatement);
//		modifiesClass.getActions().set(index, additionStatement);
	}
}
