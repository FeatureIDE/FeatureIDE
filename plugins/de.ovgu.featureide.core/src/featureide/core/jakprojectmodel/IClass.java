/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package featureide.core.jakprojectmodel;

import java.util.LinkedList;

import mixin.AST_Program;

import org.eclipse.core.resources.IFile;

public interface IClass extends IJakElement {

	/**
	 * Returns the number of all fields
	 * 
	 * @return Number of all fields of a class
	 */
	public int getFieldCount();

	/**
	 * Returns all field of a class
	 * 
	 * @return all fields of a class
	 */
	public IField[] getFields();

	/**
	 * returns the number of methods of a class
	 * 
	 * @return Number of methods of a class
	 */
	public int getMethodCount();

	/**  
	 * Returns all methods of a class
	 * 
	 * @return methods of a class
	 */
	public IMethod[] getMethods();

	/**
	 * Returns the number of fields that are availible according
	 * to the current jakfile
	 * 
	 * @return availible number of fields according to the current jakfile
	 */
	public int getAvailableFieldCount();

	/**
	 * Returns the availible fields according to the current jakfile
	 * 
	 * @return availible fields according to the current jakfile
	 */
	public IField[] getAvailableFields();

	/**
	 * Returns the number of availible methods according to the current jakfile
	 * 
	 * @return number of methods according to the current jakfile
	 */
	public int getAvailableMethodCount();

	/**
	 * Returns the availible methods according to the current jakfile
	 * 
	 * @return availible methods according to the current jakfile
	 */
	public IMethod[] getAvailableMethods();

	/**
	 * Returns the number of fields that were declarated inside the current jakfile
	 * 
	 * @return number of fields that were declarated inside the current jakfile 
	 */
	public int getOwnFieldCount();

	/**
	 * Returns the fields that were declarated inside the current jakfile
	 * 
	 * @return fields that were declarated inside the current jakfile
	 */
	public IField[] getOwnFields();

	/**
	 * Returns the number of methods that were declarated inside the current jakfile
	 * 
	 * @return number of methods that were declarated inside the current jakfile
	 */
	public int getOwnMethodCount();

	/**
	 * Returns the methods that were declarated inside the current jakfile
	 * 
	 * @return methods that were declarated inside the current jakfile
	 */
	public IMethod[] getOwnMethods();

	/**
	 * Sets the current jakfile
	 * 
	 * @param jakfile the current jakfile
	 */
	public void setJakfile(IFile jakfile);

	/**
	 * Returns the current jakfile
	 * 
	 * @return current jakfile
	 */
	public IFile getJakfile();

	/**
	 * Updates the AST of this class
	 * 
	 * @param sources 		source files that were composed to build this class
	 * @param composedASTs 	composed ahead ASTs during the composition step
	 * @param ownASTs 		ahead ASTs of each source file without composing
	 */
	public void updateAst(LinkedList<IFile> sources, AST_Program[] composedASTs,
			AST_Program[] ownASTs);

	/**
	 * Returns the ahead ASTs of each source file without composing
	 * 
	 * @return ahead ASTs of each source file without composing
	 */
	public AST_Program[] getASTs();

	/**
	 * Returns the source files that were composed to build this class
	 * 
	 * @return source files that were composed to build this class
	 */
	public LinkedList<IFile> getSources();

}
