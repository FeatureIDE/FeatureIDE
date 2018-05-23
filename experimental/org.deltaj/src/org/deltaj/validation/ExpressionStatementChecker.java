/**
 * 
 */
package org.deltaj.validation;

import org.deltaj.deltaj.Expression;
import org.deltaj.deltaj.ExpressionStatement;
import org.deltaj.deltaj.MethodCall;
import org.deltaj.deltaj.Original;
import org.deltaj.deltaj.Selection;
import org.deltaj.deltaj.util.DeltajSwitch;
import org.eclipse.emf.ecore.EObject;

/**
 * @author bettini
 * 
 */
public class ExpressionStatementChecker extends DeltajSwitch<Boolean> {

	@Override
	public Boolean caseOriginal(Original object) {
		return true;
	}

	@Override
	public Boolean caseMethodCall(MethodCall object) {
		return true;
	}

	@Override
	public Boolean caseSelection(Selection object) {
		return doSwitch(object.getMessage());
	}

	@Override
	public Boolean defaultCase(EObject object) {
		return false;
	}

	public boolean isValid(ExpressionStatement expressionStatement) {
		Expression expression = expressionStatement.getExpression();
		if (expression == null)
			return false;
		return doSwitch(expression);
	}
}
