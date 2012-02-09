/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.featurehouse.model;

import java.util.LinkedList;

import org.eclipse.core.resources.IFile;

import de.ovgu.cide.fstgen.ast.FSTTerminal;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;

/**
 * Class builders are creating entries for the FSTModel of their special language.<br>
 * Parent Class for all Class builders.
 *
 * @see {@link JavaClassBuilder}, {@link CClassBuilder}, {@link CSClassBuilder}, 
 * 		{@link HaskellClassBuilder}
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
	 * @param terminal FSTTerminal containing the field
	 */
	void caseFieldDeclaration(FSTTerminal terminal) {}
	
	/**
	 * Creates the entry for the given method.
	 * @param terminal FSTTerminal containing the method
	 */
	void caseMethodDeclaration(FSTTerminal terminal) {}
	
	/**
	 * Creates the entry for the given constructor.
	 * @param terminal FSTTerminal containing the constructor
	 */
	void caseConstructorDeclaration(FSTTerminal terminal) {}
	
	/**
	 * Locks for the correct {@link ClassBuilder} of the given file.
	 * @return <code>ClassBuilder</code> for the given file
	 */
	public static ClassBuilder getClassBuilder(IFile file, FeatureHouseModelBuilder builder) {
		if (file.getFileExtension().equals("java")) {
			return new JavaClassBuilder(builder);
		}
		if (file.getFileExtension().equals("h") || 
				file.getFileExtension().equals("c")) {
			return new CClassBuilder(builder);
		}
		if (file.getFileExtension().equals("cs")) {
			return new CSClassBuilder(builder);
		}
		if (file.getFileExtension().equals("hs")) {
			return new HaskellClassBuilder(builder);
		}
		return new ClassBuilder(builder);
	}
	
	/**
	 * Adds the method with the given parameters to the {@link FSTModel}.
	 * @param name Name of the method
	 * @param parameterTypes Types of the parameters
	 * @param returnType Return type
	 * @param modifiers Modifiers
	 * @param body The methods body
	 * @param beginLine Start of the method at features file 
	 * @param endLine End of the method at features file
	 * @param isConstructor <code>true</code> if the method is a constructor 
	 */
	void addMethod(String name, LinkedList<String> parameterTypes, 
			String returnType, String modifiers, String body, int beginLine, int endLine, boolean isConstructor) {
		FSTMethod method = new FSTMethod(name, parameterTypes, returnType, modifiers, body, beginLine, endLine);								
		method.setOwn(modelBuilder.getCurrentFile());
		method.isConstructor = isConstructor;
		if (body.contains("original")) {
			body = body.replaceAll(" ", "");
			method.refines = body.contains("original(");
		}
		modelBuilder.getCurrentClass().add(method);
	}
}
