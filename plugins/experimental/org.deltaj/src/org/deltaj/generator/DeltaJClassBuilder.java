package org.deltaj.generator;

import java.util.LinkedList;
import java.util.List;
import org.deltaj.deltaj.FieldAddition;
import org.deltaj.deltaj.MethodAddition;
import org.deltaj.deltaj.Class;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.Field;
import org.deltaj.deltaj.Method;
import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.DeltaSubAction;
import org.deltaj.deltaj.MethodModification;
import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.FieldRemoval;
import org.deltaj.deltaj.MethodRemoval;
import org.deltaj.util.ClassCollection;
import org.deltaj.util.DeltaJUtils;
import org.deltaj.util.DeltasToApply;
import org.eclipse.xtext.EcoreUtil2;
import org.eclipse.xtext.util.PolymorphicDispatcher;
import com.google.inject.Inject;

/**
 * Synthetizes {@link Class} objects from deltas
 * 
 * @author bettini
 * 
 */
public class DeltaJClassBuilder {

	@Inject
	protected DeltasToApplyFinder deltasToApplyFinder = new DeltasToApplyFinder();

	@Inject
	protected OriginalPreProcessor originalPreProcessor = new OriginalPreProcessor();

	private PolymorphicDispatcher<Boolean> modifyClassDispatcher = PolymorphicDispatcher.createForSingleTarget("modifyClassCase", 2, 2, this);

	public ClassCollection classesToGenerate(Product product) {

		DeltasToApply deltas = deltasToApplyFinder.getDeltas(product);
		return buildClasses(deltas);
	}

	public ClassCollection buildClasses(DeltasToApply deltas) {

		ClassCollection classes = new ClassCollection();
		for (DeltaModule delta: deltas) {
			buildClasses(classes, delta);
		}
		return classes;
	}

	public void buildClasses(ClassCollection currentClasses, DeltaModule deltaToApply) {

		currentClasses.addAll(getCopyOfAddedClasses(deltaToApply));
		removeClasses(currentClasses, deltaToApply);
		modifyClasses(currentClasses, deltaToApply);
	}

	public List<Class> getCopyOfAddedClasses(DeltaModule delta) {

		List<Class> addedClasses = DeltaJUtils.getAddedClasses(delta);
		List<Class> copy = new LinkedList<Class>();
		for (Class class1: addedClasses) {
			copy.add(EcoreUtil2.clone(class1));
		}
		return copy;
	}

	public void removeClasses(ClassCollection collection, DeltaModule deltaToApply) {

		List<String> classesToRemove = DeltaJUtils.getClassesToRemove(deltaToApply);
		for (String classToRemove: classesToRemove) {
			removeClassByName(collection, classToRemove);
		}
	}

	public void removeClassByName(ClassCollection collection, String classToRemove) {

		for (Class class1: collection) {
			if (class1.getName().equals(classToRemove)) {
				collection.remove(class1);
				return;
			}
		}
	}

	public void modifyClasses(ClassCollection collection, DeltaModule delta) {

		List<ClassModification> modifiesClasses = DeltaJUtils.getDeltaModifies(delta);
		for (ClassModification modifiesClass: modifiesClasses) {
			Class classToModify = DeltaJUtils.classByName(collection, modifiesClass.getName());
			if (classToModify != null)
				modifyClass(classToModify, modifiesClass);
		}
	}

	public void modifyClass(Class classToModify, ClassModification modifiesClass) {

		if (modifiesClass.getExtends() != null)
			classToModify.setExtends(modifiesClass.getExtends());
		for (DeltaSubAction modifiesClassAction: modifiesClass.getSubActions())
			modifyClass(classToModify, modifiesClassAction);
	}

	public void modifyClass(Class classToModify, DeltaSubAction modifiesClassAction) {

		modifyClassDispatcher.invoke(classToModify, modifiesClassAction);
	}

	protected void modifyClassCase(Class classToModify, FieldAddition addsField) {

		addClonedField(classToModify, addsField.getField());
	}

	protected void addClonedField(Class classToModify, Field field) {

		classToModify.getFields().add(EcoreUtil2.clone(field));
	}

	protected void modifyClassCase(Class classToModify, MethodAddition addsMethod) {

		addClonedMethod(classToModify, addsMethod.getMethod());
	}

	protected void addClonedMethod(Class classToModify, Method method) {

		classToModify.getMethods().add(EcoreUtil2.clone(method));
	}

	protected void modifyClassCase(Class classToModify, FieldRemoval removesField) {

		Field fieldToRemove = DeltaJUtils.fieldByName(classToModify, removesField.getName());
		if (fieldToRemove != null)
			classToModify.getFields().remove(fieldToRemove);
	}

	protected void modifyClassCase(Class classToModify, MethodRemoval removesMethod) {

		removeMethod(classToModify, removesMethod.getName());
	}

	protected Method removeMethod(Class classToModify, String methodName) {

		Method methodToRemove = DeltaJUtils.methodByName(classToModify, methodName);
		if (methodToRemove != null)
			classToModify.getMethods().remove(methodToRemove);
		return methodToRemove;
	}

	protected void modifyClassCase(Class classToModify, MethodModification modifiesMethod) {

		replaceMethod(classToModify, modifiesMethod.getMethod());
	}

	public void replaceMethod(Class classToModify, Method method) {

		Method methodToReplace = removeMethod(classToModify, method.getName());
		if (methodToReplace != null) {
			boolean originalReferenced = originalPreProcessor.preprocess(methodToReplace, method);
			if (originalReferenced)
				classToModify.getMethods().add(methodToReplace);
		}
		addClonedMethod(classToModify, method);
	}

}
