/**
 * 
 */
package org.deltaj.validation;

import org.deltaj.deltaj.Expression;
import org.deltaj.deltaj.FieldSelection;
import org.deltaj.deltaj.VariableAccess;
import org.deltaj.deltaj.Selection;
import org.deltaj.deltaj.util.DeltajSwitch;
import org.eclipse.emf.ecore.EObject;

/**
 * @author bettini
 * 
 */
public class AssignmentChecker extends DeltajSwitch<Boolean> {

	@Override
	public Boolean caseFieldSelection(FieldSelection object) {
		return true;
	}

	@Override
	public Boolean caseSelection(Selection object) {
		return doSwitch(object.getMessage());
	}

	@Override
	public Boolean caseVariableAccess(VariableAccess object) {
		return true;
	}

	@Override
	public Boolean defaultCase(EObject object) {
		return false;
	}

	public boolean isAssignable(Expression expression) {
		return doSwitch(expression);
	}
}
