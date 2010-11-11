/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.core.fstmodel;

import java.util.LinkedList;

import org.eclipse.core.resources.IFile;

public interface IClass extends IFSTModelElement {

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
	 * Returns the number of public fields of a class
	 * 
	 * @return public fields of a class
	 */
	public int getPublicFieldCount();
	
	/**  
	 * Returns public fields of a class
	 * 
	 * @return public fields of a class
	 */
	public IField[] getPublicFields();
	
	/**
	 * Returns the number of public methods of a class
	 * 
	 * @return public methods of a class
	 */
	public int getPublicMethodCount();
	
	/**  
	 * Returns public methods of a class
	 * 
	 * @return public methods of a class
	 */
	public IMethod[] getPublicMethods();
	
	/**
	 * Returns the number of protected fields of a class
	 * 
	 * @return protected fields of a class
	 */
	public int getProtectedFieldCount();
	
	/**  
	 * Returns protected fields of a class
	 * 
	 * @return protected fields of a class
	 */
	public IField[] getProtectedFields();
	
	/**
	 * Returns the number of protected methods of a class
	 * 
	 * @return protected methods of a class
	 */
	public int getProtectedMethodCount();
	
	/**  
	 * Returns protected methods of a class
	 * 
	 * @return protected methods of a class
	 */
	public IMethod[] getProtectedMethods();
	
	/**
	 * Returns the number of private fields of a class
	 * 
	 * @return private fields of a class
	 */
	public int getPrivateFieldCount();
	
	/**  
	 * Returns private fields of a class
	 * 
	 * @return private fields of a class
	 */
	public IField[] getPrivateFields();
	
	/**
	 * Returns the number of private methods of a class
	 * 
	 * @return private methods of a class
	 */
	public int getPrivateMethodCount();
	
	/**  
	 * Returns private methods of a class
	 * 
	 * @return private methods of a class
	 */
	public IMethod[] getPrivateMethods();
	
	/**
	 * Returns the number of package private fields of a class
	 * 
	 * @return package private fields of a class
	 */
	public int getPackagePrivateFieldCount();
	
	/**  
	 * Returns package private fields of a class
	 * 
	 * @return package private fields of a class
	 */
	public IField[] getPackagePrivateFields();
	
	/**
	 * Returns the number of package private methods of a class
	 * 
	 * @return package private methods of a class
	 */
	public int getPackagePrivateMethodCount();
	
	/**  
	 * Returns package private methods of a class
	 * 
	 * @return package private methods of a class
	 */
	public IMethod[] getPackagePrivateMethods();

	/**
	 * Returns the number of fields that are available according
	 * to the current file
	 * 
	 * @return available number of fields according to the current file
	 */
	public int getAvailableFieldCount();

	/**
	 * Returns the available fields according to the current file
	 * 
	 * @return available fields according to the current file
	 */
	public IField[] getAvailableFields();

	/**
	 * Returns the number of available methods according to the current file
	 * 
	 * @return number of methods according to the current file
	 */
	public int getAvailableMethodCount();

	/**
	 * Returns the available methods according to the current file
	 * 
	 * @return available methods according to the current file
	 */
	public IMethod[] getAvailableMethods();

	/**
	 * Returns the number of fields that were declared inside the current file
	 * 
	 * @return number of fields that were declared inside the current file 
	 */
	public int getOwnFieldCount();

	/**
	 * Returns the fields that were declared inside the current file
	 * 
	 * @return fields that were declared inside the current file
	 */
	public IField[] getOwnFields();

	/**
	 * Returns the number of methods that were declared inside the current file
	 * 
	 * @return number of methods that were declared inside the current file
	 */
	public int getOwnMethodCount();

	/**
	 * Returns the methods that were declared inside the current file
	 * 
	 * @return methods that were declared inside the current file
	 */
	public IMethod[] getOwnMethods();

	/**
	 * Sets the current file
	 * 
	 * @param jakfile the current file
	 */
	public void setJakfile(IFile jakfile);

	/**
	 * Returns the current file
	 * 
	 * @return current file
	 */
	public IFile getJakfile();

	/**
	 * Returns the source files that were composed to build this class
	 * 
	 * @return source files that were composed to build this class
	 */
	public LinkedList<IFile> getSources();

}