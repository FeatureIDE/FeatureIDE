package org.deltaj.util;

import org.deltaj.deltaj.BasicType;
import org.deltaj.deltaj.BooleanType;
import org.deltaj.deltaj.Class;
import org.deltaj.deltaj.ClassType;
import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.IntType;
import org.deltaj.deltaj.StringType;
import org.deltaj.deltaj.Type;

/**
 * Utility functions for types
 * 
 * @author bettini
 * 
 */
public class DeltaJTypeUtils {
	public static ClassType createClassType(Class cl) {
		ClassType type = DeltajFactory.eINSTANCE.createClassType();
		type.setClassref(cl.getName());
		return type;
	}

	public static BasicType createBasicType(String basic) {
		BasicType type = DeltajFactory.eINSTANCE.createBasicType();
		type.setBasic(basic);
		return type;
	}
	
	public static IntType createIntType() {
		IntType type = DeltajFactory.eINSTANCE.createIntType();
		type.setBasic("int");
		return type;
	}
	
	public static StringType createStringType() {
		StringType type = DeltajFactory.eINSTANCE.createStringType();
		type.setBasic("String");
		return type;
	}
	
	public static BooleanType createBooleanType() {
		BooleanType type = DeltajFactory.eINSTANCE.createBooleanType();
		type.setBasic("boolean");
		return type;
	}

	/**
	 * @param type
	 * @return the string representation of the passed type (both for basic and
	 *         class types)
	 */
	public static String typeToString(Type type) {
		if (type instanceof ClassType) {
			return typeToString((ClassType) type);
		}
		if (type instanceof BasicType) {
			return typeToString((BasicType) type);
		}
		return "Unknown type: " + type;
	}

	public static String typeToString(ClassType type) {
		return (type.getClassref() != null ? type.getClassref() : "");
	}

	public static String typeToString(BasicType type) {
		return type.getBasic();
	}

	public static String getClassref(Type type) {
		if (type instanceof ClassType) {
			return ((ClassType) type).getClassref();
		}
		return null;
	}

	public static String getBasicTypeString(Type type) {
		if (type instanceof BasicType) {
			return ((BasicType) type).getBasic();
		}
		return "";
	}

}
