package org.deltaj.transformations.resolve;

import org.deltaj.deltaj.ClassRemoval;
import org.deltaj.deltaj.FieldRemoval;
import org.deltaj.deltaj.MethodRemoval;
import org.deltaj.transformations.actions.DeltaJActionFactory;
import org.deltaj.transformations.actions.IDeltaJAction;
import org.deltaj.transformations.evolution.DeltaJModuleRemover;
import org.deltaj.transformations.extract.DeltaJActionExtractor;
import org.deltaj.transformations.utils.exceptions.DeltaJException;
import org.eclipse.emf.ecore.EObject;

/**
 * Resolves the specified removal action.
 * <p>
 * Every removal action can be made obsolete by disabling all preceding delta
 * actions affecting the same target for those cases where the application
 * condition of the removal action would evaluate to true.
 * 
 * @author Oliver Richers
 */
public class DeltaJRemovalActionResolver {

	private final IDeltaJAction removalAction;

	public DeltaJRemovalActionResolver(ClassRemoval removalAction) {

		this(DeltaJActionFactory.get(removalAction));
	}

	public DeltaJRemovalActionResolver(MethodRemoval removalAction) {

		this(DeltaJActionFactory.get(removalAction));
	}

	public DeltaJRemovalActionResolver(FieldRemoval removalAction) {

		this(DeltaJActionFactory.get(removalAction));
	}

	public DeltaJRemovalActionResolver(IDeltaJAction removalAction) {

		this.removalAction = removalAction;

		checkActionType(removalAction);
	}

	private void checkActionType(IDeltaJAction removalAction) {

		EObject actionStatement = removalAction.getActionStatement();

		if (actionStatement instanceof ClassRemoval || actionStatement instanceof MethodRemoval
				|| actionStatement instanceof FieldRemoval) {
			// okay
		} else {
			throw new DeltaJException("The given action is not a removal action: %s", actionStatement
					.getClass()
					.getCanonicalName());
		}
	}

	public void resolve() {

		extractRemovalActionIfNecessary();

		disablePrecedingActions();

		removeDeltaModule();
	}

	private void extractRemovalActionIfNecessary() {

		new DeltaJActionExtractor(removalAction).extractIfNecessary();
	}

	private void disablePrecedingActions() {

		new PrecedingActionsDisabler(removalAction).disable();
	}

	private void removeDeltaModule() {

		new DeltaJModuleRemover(removalAction.getDeltaModule()).remove();
	}
}
