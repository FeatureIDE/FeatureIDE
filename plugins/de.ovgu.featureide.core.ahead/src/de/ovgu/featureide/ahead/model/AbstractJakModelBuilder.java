/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ahead.model;

import java.util.LinkedList;

import org.eclipse.core.resources.IFile;

/**
 * This builder builds the JakProjectModel, by extracting features, 
 * methods and fields from classes to build. 
 * 
 * @author Tom Brosch
 * @author Constanze Adler
 * @author Jens Meinicke
 */
/**
 * Hacky: jampack and mixin have their own AST... types, which are functionally equivalent
 * due to being generated from the same code.
 * 
 * @author Felix Rieger
 */
public abstract class AbstractJakModelBuilder<AST_Program_Type> {
	/**
	 * Adds a class to the jak project model
	 * 
	 * @param className
	 *            Name of the class
	 * @param sources
	 *            source files that were composed to build this class
	 * @param composedASTs
	 *            composed ahead ASTs during the composition step
	 * @param ownASTs
	 *            ahead ASTs of each source file without composing
	 */
	public abstract void addClass(String className, LinkedList<IFile> sources,
			AST_Program_Type[] composedASTs, AST_Program_Type[] ownASTs);

	public abstract void updateAst(String currentClass, LinkedList<IFile> sources,
			AST_Program_Type[] composedASTs, AST_Program_Type[] ownASTs);

	public abstract void reset();
}


