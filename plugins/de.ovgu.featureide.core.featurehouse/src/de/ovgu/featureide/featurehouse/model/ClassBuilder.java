/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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

import org.eclipse.core.resources.IFile;

import de.ovgu.cide.fstgen.ast.FSTTerminal;

/**
 * 
 * @author Jens Meinicke
 */
public class ClassBuilder {
	
	FeatureHouseModelBuilder modelBuilder;
	
	public ClassBuilder(FeatureHouseModelBuilder modelBuilder) {
		this.modelBuilder = modelBuilder;
	}

	void caseFieldDeclaration(FSTTerminal terminal) {}
	
	void caseMethodDeclaration(FSTTerminal terminal) {}
	
	void caseConstructorDeclaration(FSTTerminal terminal) {}
	
	/**
	 * @return class builder for the current file
	 */
	public static ClassBuilder getClassBuilder(IFile file, FeatureHouseModelBuilder builder) {
		if (file.getFileExtension().equals("java")) {
			return new JavaClassBuilder(builder);
		}
		if (file.getFileExtension().equals("h") || 
				file.getFileExtension().equals("c")) {
			return new CClassBuilder(builder);
		}
		// TODO#271 implement class builder for all FeatureHouse languages
		return new ClassBuilder(builder);
	}
}
