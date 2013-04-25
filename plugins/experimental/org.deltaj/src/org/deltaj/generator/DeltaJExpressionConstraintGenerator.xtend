package org.deltaj.generator

import com.google.inject.Inject
import java.util.LinkedList
import org.deltaj.deltaj.AndOrExpression
import org.deltaj.deltaj.ArithmeticSigned
import org.deltaj.deltaj.BooleanNegation
import org.deltaj.deltaj.Cast
import org.deltaj.deltaj.Comparison
import org.deltaj.deltaj.Expression
import org.deltaj.deltaj.Field
import org.deltaj.deltaj.FieldSelection
import org.deltaj.deltaj.Message
import org.deltaj.deltaj.MethodCall
import org.deltaj.deltaj.Minus
import org.deltaj.deltaj.MultiOrDiv
import org.deltaj.deltaj.New
import org.deltaj.deltaj.Paren
import org.deltaj.deltaj.Plus
import org.deltaj.deltaj.Selection
import org.deltaj.deltaj.Type
import org.deltaj.deltaj.TypedDeclaration
import org.deltaj.deltaj.VariableAccess
import org.deltaj.typing.DeltaJTypeSystem
import org.deltaj.util.DeltaJTypeUtils
import org.eclipse.xtend2.lib.StringConcatenation

class DeltaJExpressionConstraintGenerator {
	
	DeltaJTypeSystem typeSystem
	
	StringConcatenation buffer
	
	@Inject DeltaJConstraintGeneratorHelper constraintGeneratorHelper
	
	def void init(DeltaJTypeSystem ts, StringConcatenation buf) {
		typeSystem = ts
		buffer = buf
	}

	def genConstraints(DeltaJTypeSystem ts, Expression exp) {
		init(ts, new StringConcatenation())
		genConstraintAndGetType(exp)
		buffer
	}
	
	def Type genConstraintAndGetType(DeltaJTypeSystem ts, StringConcatenation buffer, Expression exp) {
		init(ts, buffer)
		genConstraintAndGetType(exp)
	}
	
	def Type genConstraintAndGetType(Expression exp) {
		genConstraintAndGetTypeCase(exp)
	}
	
	def dispatch Type genConstraintAndGetTypeCase(Expression exp) {
		return typeSystem.getMethodBodyExpressionType(exp)
	}
	
	def dispatch Type genConstraintAndGetTypeCase(Plus exp) {
		var leftType = genConstraintAndGetType(exp.left)
		buffer.newLineIfNotEmpty
		var rightType = genConstraintAndGetType(exp.right)
		buffer.newLineIfNotEmpty
		var plusType = typeSystem.createTypeVariable
		buffer.append(constraintGeneratorHelper.genPlusConstraint(leftType, rightType, plusType, exp))
		plusType
	}
	
	def dispatch Type genConstraintAndGetTypeCase(Minus exp) {
		var intType = DeltaJTypeUtils::createIntType
		genConstraintsForSubexpressions(exp, exp.left, exp.right, intType)
		intType
	}
	
	def dispatch Type genConstraintAndGetTypeCase(MultiOrDiv exp) {
		var intType = DeltaJTypeUtils::createIntType
		genConstraintsForSubexpressions(exp, exp.left, exp.right, intType)
		intType
	}
	
	def dispatch Type genConstraintAndGetTypeCase(AndOrExpression exp) {
		var booleanType = DeltaJTypeUtils::createBooleanType
		genConstraintsForSubexpressions(exp, exp.left, exp.right, booleanType)
		booleanType
	}
	
	def dispatch Type genConstraintAndGetTypeCase(Comparison exp) {
		var booleanType = DeltaJTypeUtils::createBooleanType
		genConstraintsForSubexpressions(exp, exp.left, exp.right, DeltaJTypeUtils::createIntType)
		booleanType
	}
	
	def genConstraintsForSubexpressions(Expression main, Expression left, Expression right, Type expectedType) {
		var leftType = genConstraintAndGetType(left)
		buffer.newLineIfNotEmpty
		buffer.append(constraintGeneratorHelper.genSubtypeConstraint(leftType, expectedType, left))
		buffer.newLineIfNotEmpty
		var rightType = genConstraintAndGetType(right)
		buffer.newLineIfNotEmpty
		buffer.append(constraintGeneratorHelper.genSubtypeConstraint(rightType, expectedType, right))
		buffer.newLineIfNotEmpty
		buffer.append(constraintGeneratorHelper.genComment(main))
	}

	def dispatch Type genConstraintAndGetTypeCase(ArithmeticSigned exp) {
		var intType = DeltaJTypeUtils::createIntType
		genConstraintsForSubexpressions(exp, exp.expression, intType)
		intType
	}
	
	def dispatch Type genConstraintAndGetTypeCase(BooleanNegation exp) {
		var booleanType = DeltaJTypeUtils::createBooleanType
		genConstraintsForSubexpressions(exp, exp.expression, booleanType)
		booleanType
	}
	
	def genConstraintsForSubexpressions(Expression main, Expression subExp, Type expectedType) {
		var subExpType = genConstraintAndGetType(subExp)
		buffer.newLineIfNotEmpty
		buffer.append(constraintGeneratorHelper.genSubtypeConstraint(subExpType, expectedType, subExp))
		buffer.newLineIfNotEmpty
		buffer.append(constraintGeneratorHelper.genComment(main))
	}
	
	def dispatch Type genConstraintAndGetTypeCase(New exp) {
		buffer.append(constraintGeneratorHelper.genClassConstraint(exp.class_, exp))
		typeSystem.getMethodBodyExpressionType(exp)
	}
	
	def dispatch Type genConstraintAndGetTypeCase(Cast exp) {
		var tempBuffer = buffer
		buffer = new StringConcatenation();
		var objectType = genConstraintAndGetType(exp.object)
		if (buffer.length > 0)
			buffer.newLine
		tempBuffer.append(buffer)
		buffer = tempBuffer
		buffer.append(constraintGeneratorHelper.genCastConstraint(exp.type, objectType, exp))
		typeSystem.getMethodBodyExpressionType(exp)
	}
	
	def dispatch Type genConstraintAndGetTypeCase(Paren paren) {
		genConstraintAndGetTypeCase(paren.expression)
	}
	
	def dispatch Type genConstraintAndGetTypeCase(VariableAccess variableAccess) {
		variableAccess.genConstraintAndGetTypeCase(variableAccess.variable)
	}
	
	def dispatch Type genConstraintAndGetTypeCase(VariableAccess variableAccess, TypedDeclaration declaration) {
		declaration.type
	}

	def dispatch Type genConstraintAndGetTypeCase(VariableAccess variableAccess, Field field) {
		buffer.append(constraintGeneratorHelper.genFieldConstraint
			(typeSystem.getThisType(variableAccess), field.name, field.type, variableAccess))
		field.type
	}
	
	def dispatch Type genConstraintAndGetTypeCase(Selection sel) {
		var tempBuffer = buffer
		buffer = new StringConcatenation();
		var receiverType = genConstraintAndGetType(sel.receiver)
		if (buffer.length > 0)
			buffer.newLine
		tempBuffer.append(buffer)
		buffer = tempBuffer
		genConstraintAndGetTypeCase(receiverType, sel.message, sel)
	}
	
	def dispatch Type genConstraintAndGetTypeCase(Type receiverType, Message message, Selection sel) {
		null // should not be called
	}
	
	def dispatch Type genConstraintAndGetTypeCase(Type receiverType, FieldSelection fieldSel, Selection sel) {
		var fieldType = typeSystem.createTypeVariable
		buffer.append(constraintGeneratorHelper.genFieldConstraint(receiverType, fieldSel.field, fieldType, sel))
		fieldType
	}
	
	def dispatch Type genConstraintAndGetTypeCase(Type receiverType, MethodCall methodCall, Selection sel) {
		var methodReturnType = typeSystem.createTypeVariable
		var typesForParams = new LinkedList<Type>()
		for (arg : methodCall.args) {
			var typeForParam = typeSystem.createTypeVariable()
			var typeOfArg = genConstraintAndGetType(arg)
			buffer.newLineIfNotEmpty
			typesForParams.add(typeForParam)
			buffer.append(constraintGeneratorHelper.genSubtypeConstraint(typeOfArg, typeForParam, arg))
			buffer.newLineIfNotEmpty
		}
		buffer.append(constraintGeneratorHelper.genMethodConstraint(receiverType, methodCall.method, methodReturnType, typesForParams, sel))
		methodReturnType
	}
	
}