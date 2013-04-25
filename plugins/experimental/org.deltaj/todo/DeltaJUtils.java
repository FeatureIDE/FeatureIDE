/**
 * 
 */
package org.deltaj.util;

import java.util.List;

import org.deltaj.deltaj.AddsClass;
import org.deltaj.deltaj.AddsField;
import org.deltaj.deltaj.AddsMethod;
import org.deltaj.deltaj.Class;
import org.deltaj.deltaj.Delta;
import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.ModifiesClass;
import org.deltaj.deltaj.ModifiesMethod;
import org.deltaj.deltaj.Program;
import org.deltaj.deltaj.RemovesClass;
import org.deltaj.deltaj.RemovesField;
import org.deltaj.deltaj.RemovesMethod;
import org.eclipse.xtext.EcoreUtil2;

/**
 * @author bettini
 * 
 */
public class DeltaJUtils {

	public static List<Class> getClasses(Program program) {
		return EcoreUtil2.getAllContentsOfType(program, Class.class);
	}

	public static List<Delta> getDeltas(Program program) {
		return EcoreUtil2.typeSelect(program.getDeclarations(), Delta.class);
	}

	public static List<AddsClass> getDeltaAdds(Delta delta) {
		return EcoreUtil2.typeSelect(delta.getActions(), AddsClass.class);
	}

	public static List<ModifiesClass> getDeltaModifies(Delta delta) {
		return EcoreUtil2.typeSelect(delta.getActions(), ModifiesClass.class);
	}

	public static List<RemovesClass> getDeltaRemoves(Delta delta) {
		return EcoreUtil2.typeSelect(delta.getActions(), RemovesClass.class);
	}

	public static List<AddsField> getDeltaModifiesAddsFields(
			ModifiesClass modifiesClass) {
		return EcoreUtil2.typeSelect(modifiesClass.getActions(),
				AddsField.class);
	}

	public static List<AddsMethod> getDeltaModifiesAddsMethods(
			ModifiesClass modifiesClass) {
		return EcoreUtil2.typeSelect(modifiesClass.getActions(),
				AddsMethod.class);
	}

	public static List<RemovesField> getDeltaModifiesRemovesFields(
			ModifiesClass modifiesClass) {
		return EcoreUtil2.typeSelect(modifiesClass.getActions(),
				RemovesField.class);
	}

	public static List<RemovesMethod> getDeltaModifiesRemovesMethods(
			ModifiesClass modifiesClass) {
		return EcoreUtil2.typeSelect(modifiesClass.getActions(),
				RemovesMethod.class);
	}

	public static List<ModifiesMethod> getDeltaModifiesModifiesMethods(
			ModifiesClass modifiesClass) {
		return EcoreUtil2.typeSelect(modifiesClass.getActions(),
				ModifiesMethod.class);
	}

	public static Class createClass(String name, Class superClass) {
		Class c = DeltajFactory.eINSTANCE.createClass();
		c.setName(name);
		c.setExtends(superClass);
		return c;
	}
	
	public static Class createClass(String name) {
		return createClass(name, null);
	}
}
