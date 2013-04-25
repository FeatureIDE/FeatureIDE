package org.deltaj.generator

import com.google.inject.Inject
import java.util.List
import org.deltaj.deltaj.Expression
import org.deltaj.deltaj.JavaVerbatim
import org.deltaj.deltaj.Statement
import org.deltaj.deltaj.Type
import org.deltaj.util.DeltaJNodeModelUtils
import org.deltaj.deltaj.New
import org.deltaj.deltaj.Cast

class DeltaJConstraintGeneratorHelper {
	
	@Inject DeltaJNodeModelUtils nodeModelUtils
	
	@Inject extension DeltaJTypeGenerator typeGenerator
	
	@Inject extension DeltaJGeneratorExtensions

	def dispatch genComment(Statement statement)
		'''/* «nodeModelUtils.getProgramText(statement)» */'''
		
	def dispatch genComment(JavaVerbatim javaVerbatim) {
		javaVerbatim.javaVerbatimLines.map(line | "// " + line).join("\n")	
	}
	
	def genComment(Expression exp)
		'''// «nodeModelUtils.getProgramText(exp)»'''

	def genClassConstraint(String class_, New new_)
		'''class(«class_») «new_.genComment»'''
	
	def genSubtypeConstraint(Type candidate, Type expectedType, Expression exp) 
		'''subtype(«candidate.compileType», «expectedType.compileType») «exp.genComment»'''
	
	def genPlusConstraint(Type left, Type right, Type plusType, Expression exp) 
		'''plus(«left.compileType», «right.compileType», «plusType.compileType») «exp.genComment»'''

	def genCastConstraint(String castTo, Type candidate, Cast cast)
		'''cast(«castTo», «candidate.compileType») «cast.genComment»'''
	
	def genFieldConstraint(Type containingType, String fieldName, Type fieldType, Expression exp)
		'''field(«containingType.compileType», «fieldName», «fieldType.compileType») «exp.genComment»'''
	
	def genMethodConstraint(Type receiverType, String methodName, Type returnType, List<Type> typesForParams, Expression exp)
		'''method(«receiverType.compileType», «methodName», («typesForParams.map(t | t.compileType).join(", ")») -> «returnType.compileType») «exp.genComment»'''
	
}