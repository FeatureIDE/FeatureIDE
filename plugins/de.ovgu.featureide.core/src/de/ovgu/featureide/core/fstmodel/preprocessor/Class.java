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
package de.ovgu.featureide.core.fstmodel.preprocessor;

import java.util.LinkedList;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.fstmodel.IClass;
import de.ovgu.featureide.core.fstmodel.IFSTModelElement;
import de.ovgu.featureide.core.fstmodel.IField;
import de.ovgu.featureide.core.fstmodel.IMethod;


/**
 *	TODO Refactor models
 * Describes a class of a featureproject according to a selected configuration
 * 
 * @author Tom Brosch
 * @author Thomas Thuem
 * 
 */
public class Class implements IClass {

	// Only the own AST methods are implemented

	private IFile currentFile;

	private String className;

	private LinkedList<IFile> sources;

	public Class() {
		this("");
	}

	/**
	 * Creates a new instance of a class
	 * 
	 * @param className
	 *            The name of the class
	 */
	public Class(String className) {
		this.className = className;
	}

	public void setFile(IFile file) {
		currentFile = file;
	}

	public IFile getFile() {
		return currentFile;
	}

	public String getName() {
		return className;
	}

	public IFSTModelElement[] getChildren() {
		IFSTModelElement[] elements = new IFSTModelElement[getOwnFieldCount()
				+ getOwnMethodCount()];
		IField[] fieldArray = getOwnFields();
		IMethod[] methodArray = getOwnMethods();
		int pos = 0;
		for (int i = 0; i < fieldArray.length; i++, pos++)
			elements[pos] = fieldArray[i];
		for (int i = 0; i < methodArray.length; i++, pos++)
			elements[pos] = methodArray[i];
		return elements;
	}

	public boolean hasChildren() {
		return getOwnMethodCount() + getOwnFieldCount() > 0;
	}

	public LinkedList<IFile> getSources() {
		return sources;
	}

	/**
	 * @param file
	 */
	public void setName(String name) {
		className = name;
	}

	public IFSTModelElement getParent() {
		return null;
	}

	public int getFieldCount() {
		return 0;
	}

	public IField[] getFields() {
		return null;
	}

	public int getMethodCount() {
		return 0;
	}

	public IMethod[] getMethods() {
		return null;
	}

	public int getPublicFieldCount() {
		return 0;
	}

	public IField[] getPublicFields() {
		return null;
	}

	public int getPublicMethodCount() {
		return 0;
	}

	public IMethod[] getPublicMethods() {
		return null;
	}

	public int getProtectedFieldCount() {
		return 0;
	}

	public IField[] getProtectedFields() {
		return null;
	}

	public int getProtectedMethodCount() {
		return 0;
	}

	public IMethod[] getProtectedMethods() {
		return null;
	}

	public int getPrivateFieldCount() {
		return 0;
	}

	public IField[] getPrivateFields() {
		return null;
	}

	public int getPrivateMethodCount() {
		return 0;
	}

	public IMethod[] getPrivateMethods() {
		return null;
	}

	public int getPackagePrivateFieldCount() {
		return 0;
	}

	public IField[] getPackagePrivateFields() {
		return null;
	}

	public int getPackagePrivateMethodCount() {
		return 0;
	}

	public IMethod[] getPackagePrivateMethods() {
		return null;
	}

	public int getAvailableFieldCount() {
		return 0;
	}

	public IField[] getAvailableFields() {
		return null;
	}

	public int getAvailableMethodCount() {
		return 0;
	}

	public IMethod[] getAvailableMethods() {
		return null;
	}

	public int getOwnFieldCount() {
		return 0;
	}

	public IField[] getOwnFields() {
		return null;
	}

	public int getOwnMethodCount() {
		return 0;
	}

	public IMethod[] getOwnMethods() {
		return null;
	}
}
