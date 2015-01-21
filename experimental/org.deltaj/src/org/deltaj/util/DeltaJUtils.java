/**
 * 
 */
package org.deltaj.util;

import java.util.LinkedList;
import java.util.List;

import org.deltaj.deltaj.ClassAddition;
import org.deltaj.deltaj.FieldAddition;
import org.deltaj.deltaj.MethodAddition;
import org.deltaj.deltaj.Class;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.Expression;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.Field;
import org.deltaj.deltaj.FieldSelection;
import org.deltaj.deltaj.JavaVerbatim;
import org.deltaj.deltaj.Message;
import org.deltaj.deltaj.Method;
import org.deltaj.deltaj.Selection;
import org.deltaj.deltaj.StatementBlock;
import org.deltaj.deltaj.Statement;
import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.MethodModification;
import org.deltaj.deltaj.Original;
import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.Program;
import org.deltaj.deltaj.ClassRemoval;
import org.deltaj.deltaj.FieldRemoval;
import org.deltaj.deltaj.MethodRemoval;
import org.deltaj.deltaj.ReturnStatement;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.deltaj.This;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.EcoreUtil2;

/**
 * @author bettini
 * 
 */
public class DeltaJUtils {

	public static List<Class> getClasses(Program program) {
		return EcoreUtil2.getAllContentsOfType(program, Class.class);
	}

	public static List<Method> getMethods(Program program) {
		return EcoreUtil2.getAllContentsOfType(program, Method.class);
	}

	public static List<DeltaModule> getDeltas(Program program) {
		return EcoreUtil2.typeSelect(program.getDeltaModules(), DeltaModule.class);
	}

	public static List<ClassAddition> getDeltaAdds(DeltaModule delta) {
		return EcoreUtil2.typeSelect(delta.getDeltaActions(), ClassAddition.class);
	}

	public static List<ClassModification> getDeltaModifies(DeltaModule delta) {
		return EcoreUtil2.typeSelect(delta.getDeltaActions(), ClassModification.class);
	}

	public static List<ClassRemoval> getDeltaRemoves(DeltaModule delta) {
		return EcoreUtil2.typeSelect(delta.getDeltaActions(), ClassRemoval.class);
	}

	public static List<FieldAddition> getDeltaModifiesAddsFields(
			ClassModification modifiesClass) {
		return EcoreUtil2.typeSelect(modifiesClass.getSubActions(),
				FieldAddition.class);
	}

	public static List<MethodAddition> getDeltaModifiesAddsMethods(
			ClassModification modifiesClass) {
		return EcoreUtil2.typeSelect(modifiesClass.getSubActions(),
				MethodAddition.class);
	}

	public static List<FieldRemoval> getDeltaModifiesRemovesFields(
			ClassModification modifiesClass) {
		return EcoreUtil2.typeSelect(modifiesClass.getSubActions(),
				FieldRemoval.class);
	}

	public static List<MethodRemoval> getDeltaModifiesRemovesMethods(
			ClassModification modifiesClass) {
		return EcoreUtil2.typeSelect(modifiesClass.getSubActions(),
				MethodRemoval.class);
	}

	public static List<MethodModification> getDeltaModifiesModifiesMethods(
			ClassModification modifiesClass) {
		return EcoreUtil2.typeSelect(modifiesClass.getSubActions(),
				MethodModification.class);
	}

	public static List<Feature> getFeatures(EObject context) {
		LinkedList<Feature> result = new LinkedList<Feature>();
		if (context == null) {
			return result;
		}

		Program program = EcoreUtil2.getContainerOfType(context, Program.class);
		if (program == null) {
			return result;
		}

		return EcoreUtil2.getAllContentsOfType(program, Feature.class);
	}
	
	public static Method getContainingMethod(Statement statement) {
		return EcoreUtil2.getContainerOfType(statement, Method.class);
	}

	public static Selection createFieldSelectionOnThis(String fieldName) {
		FieldSelection fieldSelection = DeltajFactory.eINSTANCE
				.createFieldSelection();
		fieldSelection.setField(fieldName);
		return createSelection(createThis(), fieldSelection);
	}

	public static Selection createSelectionOnThis(Message message) {
		return createSelection(createThis(), message);
	}

	public static This createThis() {
		This thiz = DeltajFactory.eINSTANCE.createThis();
		thiz.setVariable("this");
		return thiz;
	}

	public static Selection createSelection(Expression receiver, Message message) {
		Selection selection = DeltajFactory.eINSTANCE.createSelection();
		selection.setReceiver(receiver);
		selection.setMessage(message);
		return selection;
	}

	public static Class createClass(String name, String superClass) {
		Class c = DeltajFactory.eINSTANCE.createClass();
		c.setName(name);
		c.setExtends(superClass);
		return c;
	}

	public static Class createClass(String name) {
		return createClass(name, null);
	}

	public static Field createField(String string) {
		Field f = DeltajFactory.eINSTANCE.createField();
		f.setName(string);
		return f;
	}

	public static Method createMethod(String string) {
		Method m = DeltajFactory.eINSTANCE.createMethod();
		m.setName(string);
		return m;
	}

	public static Feature createFeature(String name) {
		Feature feature = DeltajFactory.eINSTANCE.createFeature();
		feature.setName(name);
		return feature;
	}

	public static DeltaModule createDelta(String name) {
		DeltaModule delta = DeltajFactory.eINSTANCE.createDeltaModule();
		delta.setName(name);
		return delta;
	}

	public static Product createProduct(String name) {
		Product product = DeltajFactory.eINSTANCE.createProduct();
		product.setName(name);
		return product;
	}

	public static ProductLine createSPL(String name) {
		ProductLine spl = DeltajFactory.eINSTANCE.createProductLine();
		spl.setName(name);
		return spl;
	}

	public static Program createProgram() {
		return DeltajFactory.eINSTANCE.createProgram();
	}

	public static StatementBlock createVerbatimMethodBody(String verbatim) {
		StatementBlock statementBlock = DeltajFactory.eINSTANCE
				.createStatementBlock();
		statementBlock.getStatements().add(createVerbatim(verbatim));
		return statementBlock;
	}

	public static Original createOriginal() {
		Original original = DeltajFactory.eINSTANCE.createOriginal();
		original.setMethod("original");
		return original;
	}

	public static ReturnStatement createReturn(Expression expression) {
		ReturnStatement returnStatement = DeltajFactory.eINSTANCE
				.createReturnStatement();
		returnStatement.setExpression(expression);
		return returnStatement;
	}

	public static Statement createVerbatim(String verbatim) {
		JavaVerbatim javaVerbatim = DeltajFactory.eINSTANCE
				.createJavaVerbatim();
		javaVerbatim.setVerbatim(verbatim);
		return javaVerbatim;
	}

	public static List<ModuleReference> getDeltaModules(ProductLine spl) {
		return EcoreUtil2.getAllContentsOfType(spl, ModuleReference.class);
	}

	public static List<ModuleReference> getDeltaModules(Product product) {
		ProductLine spl = product.getProductLine();
		if (spl == null)
			return new LinkedList<ModuleReference>();
		return getDeltaModules(spl);
	}

	public static Class classByName(List<Class> classes, final String className) {
		for (Class class1 : classes) {
			if (class1.getName().equals(className))
				return class1;
		}
		return null;
	}

	public static Field fieldByName(Class clazz, final String fieldName) {
		for (Field field : clazz.getFields()) {
			if (field.getName().equals(fieldName))
				return field;
		}
		return null;
	}

	public static Method methodByName(Class clazz, final String methodName) {
		for (Method method : clazz.getMethods()) {
			if (method.getName().equals(methodName))
				return method;
		}
		return null;
	}

	public static Product productByName(Program program,
			final String productName) {
		for (Product product : program.getProducts()) {
			if (product.getName().equals(productName))
				return product;
		}
		return null;
	}

	public static List<Class> getAddedClasses(ModuleReference deltaModule) {
		DeltaModule delta = deltaModule.getDeltaModule();
		if (delta == null)
			return new LinkedList<Class>();
		return getAddedClasses(delta);
	}

	public static List<Class> getAddedClasses(DeltaModule delta) {
		List<ClassAddition> addsClasses = DeltaJUtils.getDeltaAdds(delta);
		List<Class> classes = new LinkedList<Class>();
		for (ClassAddition addsClass : addsClasses) {
			classes.add(addsClass.getClass_());
		}
		return classes;
	}

	public static List<String> getClassesToRemove(DeltaModule delta) {
		List<String> classesToRemove = new LinkedList<String>();
		List<ClassRemoval> removesClasses = DeltaJUtils.getDeltaRemoves(delta);
		for (ClassRemoval removesClass : removesClasses) {
			classesToRemove.add(removesClass.getName());
		}
		return classesToRemove;
	}

}
