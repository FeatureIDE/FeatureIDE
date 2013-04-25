/**
 * 
 */
package org.deltaj.typing;

import it.xtypes.runtime.TypeSystemResult;
import it.xtypes.runtime.TypingJudgmentEnvironment;

import org.deltaj.deltaj.Class;
import org.deltaj.deltaj.Expression;
import org.deltaj.deltaj.Method;
import org.deltaj.deltaj.Type;
import org.deltaj.deltaj.TypeVariable;
import org.deltaj.typesystem.deltaj.DeltaJTypeSystemDefinition;
import org.deltaj.util.DeltaJTypeUtils;
import org.deltaj.util.DeltaJUtils;
import org.eclipse.xtext.EcoreUtil2;

import com.google.inject.Inject;

/**
 * @author bettini
 * 
 */
public class DeltaJTypeSystem {

	@Inject
	protected DeltaJTypeSystemDefinition generatedTypeSystem;

	@Inject
	protected TypeVariableGenerator typeVariableGenerator;

	public Type getMethodBodyExpressionType(Expression expression) {
		return getType(getEnvironmentFor(expression), expression);
	}

	public Type getType(TypingJudgmentEnvironment environment,
			Expression expression) {
		TypeSystemResult<Type> result = generatedTypeSystem.typeAsType(
				environment, expression);
		return (result.getValue() != null ? result.getValue()
				: typeVariableGenerator.createTypeVariable());
	}

	/**
	 * Returns the type of 'this' in the method containing the passed expression
	 * 
	 * @param expression
	 * @return
	 */
	public Type getThisType(Expression expression) {
		return getType(getEnvironmentFor(expression), DeltaJUtils.createThis());
	}

	public TypingJudgmentEnvironment getEnvironmentFor(Expression expression) {
		return getEnvironmentFor(EcoreUtil2.getContainerOfType(expression,
				Method.class));
	}

	public TypingJudgmentEnvironment getEnvironmentFor(Method method) {
		TypingJudgmentEnvironment environment = new TypingJudgmentEnvironment();
		if (method == null)
			return environment;
		Class containingClass = EcoreUtil2.getContainerOfType(method,
				Class.class);
		if (containingClass != null)
			environment.add("this",
					DeltaJTypeUtils.createClassType(containingClass));
		return environment;
	}

	public TypeVariable createTypeVariable() {
		return typeVariableGenerator.createTypeVariable();
	}
}
