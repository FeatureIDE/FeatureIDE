package org.deltaj.transformations.actions;

import java.util.Map;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.Program;
import org.deltaj.transformations.modules.references.DeltaJModuleReference;
import org.eclipse.emf.ecore.EObject;

/**
 * Common interface of all delta actions and delta sub actions.
 * 
 * @see IDeltaJClassAction
 * @see IDeltaJClassSubAction
 * @author Oliver Richers
 */
public interface IDeltaJAction {

	IDeltaJClassAction getParentAction();

	EObject getActionStatement();

	DeltaModule getDeltaModule();

	Program getProgram();

	DeltaJActionType getActionType();

	DeltaJActionTargetType getTargetType();

	String getTargetName();

	Map<String, DeltaJModuleReference> findModuleReferences();
}
