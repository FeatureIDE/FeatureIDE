package org.deltaj.validation;

import java.util.Collection;

import org.deltaj.deltaj.Assignment;
import org.deltaj.deltaj.Cast;
import org.deltaj.deltaj.DeltajPackage;
import org.deltaj.deltaj.ExpressionStatement;
import org.deltaj.deltaj.FieldSelection;
import org.deltaj.deltaj.Method;
import org.deltaj.deltaj.MethodCall;
import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.MethodModification;
import org.deltaj.deltaj.New;
import org.deltaj.deltaj.Null;
import org.deltaj.deltaj.FieldRemoval;
import org.deltaj.deltaj.MethodRemoval;
import org.deltaj.deltaj.RemovesOrModifiesClass;
import org.deltaj.deltaj.ReturnStatement;
import org.deltaj.deltaj.Selection;
import org.deltaj.deltaj.TypeForMethod;
import org.deltaj.deltaj.VoidType;
import org.deltaj.util.DeltaJElementCollector;
import org.deltaj.util.DeltaJUtils;
import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.xtext.validation.Check;

import com.google.inject.Inject;

public class DeltaJJavaValidator extends AbstractDeltaJJavaValidator {

	@Inject
	protected ExpressionStatementChecker expressionStatementChecker;

	@Inject
	protected AssignmentChecker assignmentChecker;

	@Inject
	protected DeltaJElementCollector collector;

	public static final String CANNOT_PERFORM_SELECTION_ON_NULL_MESSAGE = "Cannot perform selection on 'null'";

	public static final String INVALID_EXPRESSION_STATEMENT_MESSAGE = "Invalid expression statement";

	public static final String INVALID_ASSIGNABLE_EXPRESSION = "Invalid left assign expression";

	public static final String CLASS_IS_NEVER_ADDED = "class is never added: ";

	public static final String FIELD_IS_NEVER_ADDED = "field is never added: ";

	public static final String METHOD_IS_NEVER_ADDED = "method is never added: ";

	public static final String VOID_METHOD_RETURN = "void method cannot return an expression";

	public static final String NON_VOID_METHOD_RETURN = "method must return an expression";

	@Check
	public void checkMessagesOnNull(Selection selection) {
		if (selection.getReceiver() instanceof Null) {
			error(CANNOT_PERFORM_SELECTION_ON_NULL_MESSAGE,
					DeltajPackage.Literals.SELECTION__RECEIVER);
		}
	}

	@Check
	public void checkExpressionStatement(ExpressionStatement expressionStatement) {
		if (!expressionStatementChecker.isValid(expressionStatement))
			error(INVALID_EXPRESSION_STATEMENT_MESSAGE,
					DeltajPackage.Literals.EXPRESSION_STATEMENT
							.getEIDAttribute());
	}

	@Check
	public void checkAssignment(Assignment assignment) {
		if (!assignmentChecker.isAssignable(assignment.getLeft()))
			error(INVALID_ASSIGNABLE_EXPRESSION,
					DeltajPackage.Literals.ASSIGNMENT__LEFT);
	}

	@Check
	public void checkClassExistenceOfRemovesOrModifiesClass(
			RemovesOrModifiesClass removesOrModifiesClass) {
		issueErrorIfClassDoesNotExist(removesOrModifiesClass,
				removesOrModifiesClass.getName(),
				DeltajPackage.Literals.REMOVES_OR_MODIFIES_CLASS__NAME);
	}

	@Check
	public void checkClassExistenceOfNew(New context) {
		issueErrorIfClassDoesNotExist(context, context.getClass_(),
				DeltajPackage.Literals.NEW__CLASS);
	}

	@Check
	public void checkAddedClass(org.deltaj.deltaj.Class clazz) {
		issueErrorIfClassDoesNotExist(clazz, clazz.getExtends(),
				DeltajPackage.Literals.CLASS__EXTENDS);
	}

	@Check
	public void checkModifiesClass(ClassModification modifiesClass) {
		issueErrorIfClassDoesNotExist(modifiesClass,
				modifiesClass.getExtends(),
				DeltajPackage.Literals.CLASS_MODIFICATION__EXTENDS);
	}

	@Check
	public void checkCast(Cast cast) {
		issueErrorIfClassDoesNotExist(cast, cast.getType(),
				DeltajPackage.Literals.CAST__TYPE);
	}

	protected void issueErrorIfClassDoesNotExist(EObject context,
			String className, EAttribute attribute) {
		Collection<String> classNames = collector
				.getAllAvailableClassNames(context);
		if (!classNames.contains(className))
			error(CLASS_IS_NEVER_ADDED + className, attribute);
	}

	@Check
	public void checkFieldSelection(FieldSelection fieldSelection) {
		issueErrorIfFieldDoesNotExist(fieldSelection,
				fieldSelection.getField(),
				DeltajPackage.Literals.FIELD_SELECTION__FIELD);
	}

	@Check
	public void checkRemovesField(FieldRemoval removesField) {
		issueErrorIfFieldDoesNotExist(removesField, removesField.getName(),
				DeltajPackage.Literals.FIELD_REMOVAL__NAME);
	}

	protected void issueErrorIfFieldDoesNotExist(EObject context,
			String fieldName, EAttribute attribute) {
		Collection<String> fieldNames = collector
				.getAllAvailableFieldNames(context);
		if (!fieldNames.contains(fieldName))
			error(FIELD_IS_NEVER_ADDED + fieldName, attribute);
	}

	@Check
	public void checkMethodSelection(MethodCall methodCall) {
		issueErrorIfMethodDoesNotExist(methodCall, methodCall.getMethod(),
				DeltajPackage.Literals.METHOD_CALL__METHOD);
	}

	@Check
	public void checkRemovesMethod(MethodRemoval removesMethod) {
		issueErrorIfMethodDoesNotExist(removesMethod, removesMethod.getName(),
				DeltajPackage.Literals.METHOD_REMOVAL__NAME);
	}

	@Check
	public void checkModifiesMethod(MethodModification modifiesMethod) {
		final Method method = modifiesMethod.getMethod();
		if (collector.getMethodsWithTheSameName(method).size() == 0)
			error(METHOD_IS_NEVER_ADDED + method.getName(),
					DeltajPackage.Literals.METHOD_MODIFICATION__METHOD);
	}

	@Check
	public void checkReturn(ReturnStatement returnStatement) {
		final Method method = DeltaJUtils.getContainingMethod(returnStatement);
		TypeForMethod returnType = method.getReturntype();
		if (returnType instanceof VoidType
				&& returnStatement.getExpression() != null) {
			error(VOID_METHOD_RETURN,
					DeltajPackage.Literals.RETURN_STATEMENT__EXPRESSION);
		} else if (!(returnType instanceof VoidType)
				&& returnStatement.getExpression() == null) {
			error(NON_VOID_METHOD_RETURN,
					DeltajPackage.Literals.RETURN_STATEMENT.getEIDAttribute());
		}
	}
	
//	@Check
//	public void checkRemovesStatements(RemovesClass removesClass) {
//		info("This could be refactored.", removesClass, null, -1, ValidationCode.REMOVES_CLASS);
//	}
//
//	@Check
//	public void checkWhenStatements(DeltaModule moduleReference) {
//		info("The formula of the application conditions could be optimized.", moduleReference, null, -1, ValidationCode.OPTIMIZE_WHEN);
//	}
//
//	@Check
//	public void checkConfigurationNotes(Configuration configuration) {
//		info("The formula of the feature configuration could be optimized.", configuration, null, -1, ValidationCode.OPTIMIZE_CONFIGURATION);
//	}
	
	protected void issueErrorIfMethodDoesNotExist(EObject context,
			String methodName, EStructuralFeature feature) {
		Collection<String> methodNames = collector
				.getAllAvailableMethodNames(context);
		if (!methodNames.contains(methodName))
			error(METHOD_IS_NEVER_ADDED + methodName, feature);
	}
}
