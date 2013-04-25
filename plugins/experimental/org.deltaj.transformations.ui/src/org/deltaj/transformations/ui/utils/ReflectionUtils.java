package org.deltaj.transformations.ui.utils;

import java.lang.reflect.Method;
import java.util.List;
import org.deltaj.transformations.utils.ListFactory;
import org.deltaj.transformations.utils.exceptions.DeltaJException;
import org.eclipse.emf.ecore.EObject;

public class ReflectionUtils {

	public static Method findMatchingMethod(Object targetObject, String methodName, List<EObject> arguments) {

		List<Method> matchingMethods = ListFactory.createArrayList();

		for (Method method: targetObject.getClass().getDeclaredMethods()) {
			if (method.getName().equals(methodName) && isInvokeable(method, arguments)) {
				matchingMethods.add(method);
			}
		}

		if (matchingMethods.size() > 1) {
			throw new DeltaJException("Found more than one matching method for '%s'.", methodName);
		}

		return matchingMethods.isEmpty()? null : matchingMethods.get(0);
	}

	public static boolean isInvokeable(Method method, List<?> arguments) {

		Class<?>[] methodParameters = method.getParameterTypes();

		if (methodParameters.length != arguments.size()) {
			return false;
		}

		for (int i = 0; i < arguments.size(); ++i) {

			if (!isAssignable(methodParameters[i], arguments.get(i))) {
				return false;
			}
		}

		return true;
	}

	public static boolean isAssignable(Class<?> parameterClass, Object argument) {

		if (argument != null) {
			return parameterClass.isAssignableFrom(argument.getClass());
		} else {
			return !parameterClass.isPrimitive();
		}
	}
}
