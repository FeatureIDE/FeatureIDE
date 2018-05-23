package org.deltaj.generator

import com.google.inject.Inject
import org.deltaj.deltaj.Class
import org.deltaj.deltaj.JavaVerbatim
import org.deltaj.deltaj.Product
import org.eclipse.xtend2.lib.StringConcatenation
import org.eclipse.xtext.util.Strings

class DeltaJGeneratorExtensions {
	
	@Inject DeltaJClassBuilder classBuilder
	
	def fileName(Product product, Class clazz) {
		packageName(product).folderName + "/" +
			clazz.name + ".java"
	}

	def packageName(Product product) {
		product.getProductLine.getName.nameToPackage.
			concatPackage(product.name.nameToPackage)
	}
	
	def qualifiedName(Product product, Class clazz) {
		packageName(product).concatPackage(clazz.name)
	}
	
	def nameToPackage(String name) {
		name.toLowerCase
	}
	
	def concatPackage(String prefix, String suffix) {
		if (prefix.nullOrEmpty) 
			suffix 
		else 
			prefix + "." + suffix
	}
	
	def folderName(String javaPackageName) {
		if (javaPackageName != null) javaPackageName.replace('.', '/') else "" 
	}
	
	def classBuilder() {
		classBuilder
	}
	
	def classesToGenerate(Product product) {
		classBuilder.classesToGenerate(product)
	}
	
	def extractJavaVerbatimCode(JavaVerbatim javaVerbatim) {
		javaVerbatim.verbatim.replace('**Java:', '').replace(':Java**', '')
	}
	
	def javaVerbatimLines(JavaVerbatim javaVerbatim) {
		Strings::split(javaVerbatim.verbatim, System::getProperty("line.separator"))
	}
	
	def addNewLineIfNotEmpty(StringConcatenation buffer) {
		if (buffer.length > 0)
			buffer.newLine
		buffer
	}
}