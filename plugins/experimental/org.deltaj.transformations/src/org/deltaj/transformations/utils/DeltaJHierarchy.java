package org.deltaj.transformations.utils;

import org.deltaj.deltaj.Class;
import org.deltaj.deltaj.ClassAddition;
import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.DeltaSubAction;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.Features;
import org.deltaj.deltaj.Field;
import org.deltaj.deltaj.Method;
import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.deltaj.Program;

public class DeltaJHierarchy {

	public static ProductLine getProductLine(Features features) {

		return (ProductLine) features.eContainer();
	}

	public static Features getFeatures(Feature feature) {

		return (Features) feature.eContainer();
	}

	public static ProductLine getProductLine(Feature feature) {

		return getProductLine(getFeatures(feature));
	}

	public static Class getClassDefinition(Method method) {

		return (Class) method.eContainer();
	}

	public static Class getClassDefinition(Field field) {

		return (Class) field.eContainer();
	}

	public static ClassAddition getClassAddition(Class class_) {

		return (ClassAddition) class_.eContainer();
	}

	public static ClassModification getClassModification(DeltaSubAction subAction) {

		return (ClassModification) subAction.eContainer();
	}

	public static Program getProgram(ProductLine productLine) {

		return (Program) productLine.eContainer();
	}

	public static Program getProgram(Product product) {

		return (Program) product.eContainer();
	}

	public static Program getProgram(DeltaModule deltaModule) {

		return (Program) deltaModule.eContainer();
	}
}
