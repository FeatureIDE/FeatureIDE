package org.deltaj.generator

import com.google.inject.Inject
import java.util.List
import org.deltaj.deltaj.Assignment
import org.deltaj.deltaj.Expression
import org.deltaj.deltaj.ExpressionStatement
import org.deltaj.deltaj.IfStatement
import org.deltaj.deltaj.ReturnStatement
import org.deltaj.deltaj.Statement
import org.deltaj.typing.DeltaJTypeSystem
import org.deltaj.util.DeltaJTypeUtils
import org.eclipse.xtend2.lib.StringConcatenation

import static extension org.deltaj.util.DeltaJUtils.*

class DeltaJStatementConstraintGenerator {
	
	DeltaJTypeSystem typeSystem
	
	@Inject DeltaJExpressionConstraintGenerator expressionConstraintGenerator
	
	@Inject DeltaJConstraintGeneratorHelper constraintGeneratorHelper
	
	@Inject extension DeltaJGeneratorExtensions generatorExtensions
	
	def genConstraints(DeltaJTypeSystem ts, List<Statement> statements) {
		typeSystem = ts
		genConstraints(statements)
	}
	
	def genConstraints(List<Statement> statements) '''
	«FOR statement : statements»
	«genConstraints(typeSystem, statement)»
	«ENDFOR»
	'''
	
	def genConstraints(DeltaJTypeSystem ts, Statement statement) {
		typeSystem = ts
		var constraints = statement.genConstraintsCase
		var comment = constraintGeneratorHelper.genComment(statement)
		if (constraints.length > 0) {
'''«comment»
«constraints»'''
		} else {
			comment
		}
	}
	
	def dispatch genConstraintsCase(Statement statement) ''''''
	
	def dispatch genConstraintsCase(ExpressionStatement statement) 
		'''«expressionConstraintGenerator.genConstraints(typeSystem, statement.expression)»'''
	
	def dispatch genConstraintsCase(ReturnStatement statement) {
		if (statement.expression != null) {
			var buffer = new StringConcatenation();
			val expType = expressionConstraintGenerator.genConstraintAndGetType(typeSystem, buffer, statement.expression)
			buffer.addNewLineIfNotEmpty
			buffer.append(constraintGeneratorHelper.genSubtypeConstraint(expType, statement.containingMethod.returntype, statement.expression))
			buffer
		} else ''''''
	}
	
	def dispatch genConstraintsCase(Assignment assignment) {
		var buffer = new StringConcatenation();
		expressionConstraintGenerator.init(typeSystem, buffer)
		var leftType = expressionConstraintGenerator.genConstraintAndGetType(assignment.left)
		buffer.addNewLineIfNotEmpty
		var rightType = expressionConstraintGenerator.genConstraintAndGetType(assignment.right)
		buffer.addNewLineIfNotEmpty
		buffer.append(constraintGeneratorHelper.genSubtypeConstraint(rightType, leftType, assignment.right))
		buffer
	}
	
	def dispatch genConstraintsCase(IfStatement statement) {
		var buffer = new StringConcatenation()
		var expressionType = expressionConstraintGenerator.genConstraintAndGetType(typeSystem, buffer, statement.expression)
		var booleanType = DeltaJTypeUtils::createBooleanType
		buffer.addNewLineIfNotEmpty
		buffer.append(constraintGeneratorHelper.genSubtypeConstraint(expressionType, booleanType, statement.expression))
		buffer.addNewLineIfNotEmpty
		buffer.append('''// then branch''')
		buffer.addNewLineIfNotEmpty
		buffer.append(genConstraints(statement.thenBlock.statements))
		if (statement.elseBlock != null) {
			buffer.newLineIfNotEmpty
			buffer.append('''// else branch''')
			buffer.addNewLineIfNotEmpty
			buffer.append(genConstraints(statement.elseBlock.statements))
		}
		buffer
	}
	
	def genConstraints(Expression exp) {
		expressionConstraintGenerator.genConstraints(typeSystem, exp)
	}

}