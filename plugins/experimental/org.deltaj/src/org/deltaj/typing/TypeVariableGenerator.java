/**
 * 
 */
package org.deltaj.typing;

import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.TypeVariable;

/**
 * @author bettini
 * 
 */
public class TypeVariableGenerator {

	protected int counter = 0;

	public TypeVariable createTypeVariable() {
		TypeVariable typeVariable = DeltajFactory.eINSTANCE
				.createTypeVariable();
		typeVariable.setVarName(createTypeVariableId());
		return typeVariable;
	}

	private String createTypeVariableId() {
		return "<" + ++counter + ">";
	}
}
