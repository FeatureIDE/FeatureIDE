package org.deltaj.generator

import org.deltaj.deltaj.Type
import org.deltaj.deltaj.TypeVariable
import org.deltaj.deltaj.ClassType
import org.deltaj.deltaj.BasicType

class DeltaJTypeGenerator {
	
	def dispatch compileType(Type type) ''''''
	
	def dispatch compileType(TypeVariable type) '''«type.varName»'''
	
	def dispatch compileType(ClassType type) '''«type.classref»'''
	
	def dispatch compileType(BasicType type) '''«type.basic»'''
}