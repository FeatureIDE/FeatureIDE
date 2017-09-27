/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 *
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.featurehouse.model;

import java.util.LinkedList;

import org.eclipse.core.resources.IFile;

import de.ovgu.cide.fstgen.ast.FSTNode;
import de.ovgu.cide.fstgen.ast.FSTNonTerminal;
import de.ovgu.cide.fstgen.ast.FSTTerminal;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.IRoleElement;

/**
 * Class builders are creating entries for the FSTModel of their special language.<br> Parent Class for all Class builders.
 *
 * @see {@link JavaClassBuilder}, {@link CClassBuilder}, {@link CSClassBuilder}, {@link HaskellClassBuilder}
 * @author Jens Meinicke
 */
public class ClassBuilder {

	/**
	 * The {@link FeatureHouseModelBuilder} calling the {@link ClassBuilder}
	 */
	FeatureHouseModelBuilder modelBuilder;

	public ClassBuilder(FeatureHouseModelBuilder modelBuilder) {
		this.modelBuilder = modelBuilder;
	}

	/**
	 * Creates the entry for the given field.
	 *
	 * @param terminal FSTTerminal containing the field
	 */
	void caseFieldDeclaration(FSTTerminal terminal) {}

	/**
	 * Creates the entry for the given method.
	 *
	 * @param terminal FSTTerminal containing the method
	 */
	void caseMethodDeclaration(FSTTerminal terminal) {}

	/**
	 * Creates the entry for the given constructor.
	 *
	 * @param terminal FSTTerminal containing the constructor
	 */
	void caseConstructorDeclaration(FSTTerminal terminal) {}

	/**
	 * Creates the entry for the given constructor.
	 *
	 * @param terminal FSTTerminal containing the constructor
	 */
	void caseInnerClassDeclaration(FSTTerminal terminal) {}

	/**
	 * Locks for the correct {@link ClassBuilder} of the given file.
	 *
	 * @return <code>ClassBuilder</code> for the given file
	 */
	public static ClassBuilder getClassBuilder(IFile file, FeatureHouseModelBuilder builder) {
		final String fileExtension = file.getFileExtension();
		if ("java".equals(fileExtension)) {
			return new JavaClassBuilder(builder);
		}
		if ("h".equals(fileExtension) || "c".equals(fileExtension)) {
			return new CClassBuilder(builder);
		}
		if ("cs".equals(fileExtension)) {
			return new CSClassBuilder(builder);
		}
		if ("hs".equals(fileExtension)) {
			return new HaskellClassBuilder(builder);
		}
		if ("asm".equals(fileExtension)) {
			return new AsmetaLClassBuilder(builder);
		}
		return new ClassBuilder(builder);
	}

	void addMethod(String name, LinkedList<String> parameterTypes, String returnType, String modifiers, String body, int beginLine, int endLine,
			boolean isConstructor) {
		addMethod(name, parameterTypes, returnType, modifiers, body, beginLine, endLine, isConstructor, "", "", -1);
	}

	/**
	 * Adds the method with the given parameters to the {@link FSTModel}.
	 *
	 * @param name Name of the method
	 * @param parameterTypes Types of the parameters
	 * @param returnType Return type
	 * @param modifiers Modifiers
	 * @param body The methods body
	 * @param beginLine Start of the method at features file
	 * @param endLine End of the method at features file
	 * @param isConstructor <code>true</code> if the method is a constructor
	 * @param contract contract string if existent
	 */
	IRoleElement addMethod(String name, LinkedList<String> parameterTypes, String returnType, String modifiers, String body, int beginLine, int endLine,
			boolean isConstructor, String contract, String compKey, int contractLine) {
		final FSTMethod method = new FSTMethod(name, parameterTypes, returnType, modifiers, body, beginLine, endLine, contract, compKey, contractLine);
		method.setConstructor(isConstructor);
		if (body.contains("original")) {
			body = body.replaceAll(" ", "");
			method.setRefines(body.contains("original("));
		}
		modelBuilder.getCurrentClassFragment().add(method);
		return method;
	}

	protected IRoleElement addField(String fieldName, String typeName, String modifiers, String body, int beginLine, int endLine) {
		final FSTField field = new FSTField(fieldName, typeName, modifiers, body, beginLine, endLine);
		modelBuilder.getCurrentClassFragment().add(field);
		return field;
	}

	public void caseJMLSpecCaseSeq(FSTTerminal terminal) {}

	public void caseClassDeclarationType(FSTTerminal terminal) {}

	public void caseAddImport(FSTTerminal terminal) {}

	public void casePackage(FSTTerminal terminal) {}

	public void caseImplementsList(FSTTerminal terminal) {}

	public void caseExtendsList(FSTTerminal terminal) {}

	public void caseModifiers(FSTTerminal terminal) {}

	public void caseInvariant(FSTTerminal terminal) {}

	public void caseInitialization(FSTNode node) {}

	public void caseSignatureDeclaration(FSTNonTerminal node) {}
}
