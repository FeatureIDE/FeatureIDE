package org.deltaj.util;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import org.deltaj.deltaj.*;
import org.deltaj.deltaj.Class;

/**
 * Utility functions for types
 * 
 * @author bettini
 * 
 */
public class DeltaJTypeUtils {
	/**
	 * Sets the type of a typed element as a class reference
	 * 
	 * @param typedElement
	 * @param cl
	 */
	public static void setTypeClassReference(TypedElement typedElement, Class cl) {
		ClassType type = createClassType(cl);
		typedElement.setType(type);
	}

	public static ClassType createClassType(Class cl) {
		ClassType type = DeltajFactory.eINSTANCE.createClassType();
		type.setClassref(cl);
		return type;
	}

	public static BasicType createBasicType(String basic) {
		BasicType type = DeltajFactory.eINSTANCE.createBasicType();
		type.setBasic(basic);
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
		return (type.getClassref() != null ? type.getClassref().getName() : "");
	}

	public static String typeToString(BasicType type) {
		return type.getBasic();
	}

	public static Class getClassref(Type type) {
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

	/**
	 * Collects all the fields of a class (including the inherited ones, which
	 * will appear first in the list).
	 * 
	 * @param cl
	 * @return the fields of a class (including the inherited ones)
	 */
	public static List<Field> getOrderedFields(Class cl) {
		return getOrderedFields(cl, cl.getExtends());
	}

	/**
	 * Collects all the fields of a class (including the inherited ones, by
	 * using the explicit base class for the hierarchy, which will appear first
	 * in the list).
	 * 
	 * @param cl
	 * @param base
	 *            the explicit base class for computing the hierarchy
	 * @return the fields of a class (including the inherited ones)
	 */
	public static List<Field> getOrderedFields(Class cl, Class base) {
		if (cl == null)
			return new LinkedList<Field>();

		List<Field> fields = new LinkedList<Field>();
		List<Class> superClasses = getClassHierarchy(cl, base);

		for (Class class1 : superClasses) {
			fields.addAll(0, class1.getFields());
		}

		return fields;
	}

	/**
	 * Collects all the methods of a class (including the inherited ones, by
	 * using the explicit base class for the hierarchy). In case of method
	 * overriding, makes sure to get the most redefined version.
	 * 
	 * @param cl
	 * @param base
	 *            the explicit base class for computing the hierarchy
	 * @return the methods of a class (including the inherited ones)
	 */
	public static List<Method> getMethods(Class cl) {
		return getMethods(cl, cl.getExtends());
	}

	/**
	 * Collects all the methods of a class (including the inherited ones). In
	 * case of method overriding, makes sure to get the most redefined version.
	 * 
	 * @param cl
	 * @return the methods of a class (including the inherited ones)
	 */
	public static List<Method> getMethods(Class cl, Class base) {
		HashMap<String, Method> methodMap = new HashMap<String, Method>();
		List<Method> result = new LinkedList<Method>();

		List<Class> superClasses = getClassHierarchy(cl, base);
		for (Class class1 : superClasses) {
			List<Method> currentClassMethods = class1.getMethods();
			for (Method method : currentClassMethods) {
				// add it only if not already present
				if (!methodMap.containsKey(method.getName())) {
					methodMap.put(method.getName(), method);
					result.add(method);
				}
			}
		}

		return result;
	}

	/**
	 * Computes the superclasses of a given class (also avoids duplicates, in
	 * case of cyclic hierarchy). The superclasses respect the hierarchy order,
	 * starting from the direct superclass up.
	 * 
	 * When iterating over a class hierarchy, you should never iterate directly
	 * over the superclass of a given class since a (malformed) class hierarchy
	 * may contain a cycle and you'd end up looping. Thus, never do:
	 * 
	 * <pre>
	 * Class current = cl;
	 * while (current != null) {
	 * 		...
	 * 		current = current.getExtends();
	 * }
	 * </pre>
	 * 
	 * Instead the classes returned by this method should be used to iterate
	 * over a class hierarchy.
	 * 
	 * @param cl
	 * @return the superclasses of a given class (without duplicates)
	 */
	public static List<Class> getOrderedSuperclasses(Class cl) {
		List<Class> orderedSuperClasses = new LinkedList<Class>();
		// only used to avoid loops.
		ClassSet superClasses = new ClassSet();

		Class current = cl.getExtends();
		while (current != null) {
			// avoid endless loops in case of cycles
			if (superClasses.contains(current))
				break;
			superClasses.add(current);
			orderedSuperClasses.add(current);
			current = current.getExtends();
		}

		return orderedSuperClasses;
	}

	public static List<Class> getClassHierarchy(Class cl) {
		return getClassHierarchy(cl, cl.getExtends());
	}

	public static List<Class> getClassHierarchy(Class cl1, Class base) {
		List<Class> hierarchy = new LinkedList<Class>();
		hierarchy.add(cl1);
		// avoid direct cycle
		if (base == null || cl1.equals(base))
			return hierarchy;
		hierarchy.add(base);
		hierarchy.addAll(getOrderedSuperclasses(base));
		return hierarchy;
	}
}
