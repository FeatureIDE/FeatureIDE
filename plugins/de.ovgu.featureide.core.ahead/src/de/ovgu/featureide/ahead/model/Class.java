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
package de.ovgu.featureide.ahead.model;

import java.util.LinkedList;
import java.util.TreeMap;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.jakprojectmodel.IClass;
import de.ovgu.featureide.core.jakprojectmodel.IField;
import de.ovgu.featureide.core.jakprojectmodel.IJakModelElement;
import de.ovgu.featureide.core.jakprojectmodel.IMethod;


/**
 * Describes a class of a jak project according to a selected equation
 * 
 * @author Tom Brosch
 * @author Thomas Thuem
 * 
 */
public class Class extends JakModelElement implements IClass {

	// Only the own AST methods are implemented

	private IFile currentJakfile;

	TreeMap<String, Method> methods;

	TreeMap<String, IField> fields;

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
		methods = new TreeMap<String, Method>();
		fields = new TreeMap<String, IField>();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.jakprojectmodel.IClass#getNumberOfFields()
	 */
	public int getFieldCount() {
		return fields.size();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.jakprojectmodel.IClass#getFields()
	 */
	public IField[] getFields() {
		return fields.values().toArray(new Field[fields.values().size()]);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.jakprojectmodel.IClass#getNumberOfMethods()
	 */
	public int getMethodCount() {
		return methods.size();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.jakprojectmodel.IClass#getMethods()
	 */
	public IMethod[] getMethods() {
		IMethod[] methodArray = new IMethod[methods.size()];
		int i = 0;
		for (IMethod meth : methods.values())
			methodArray[i++] = meth;
		return methodArray;
	}

	
	public int getPublicFieldCount() {
		int i = 0;
		for (IField field : fields.values())
			if (field.isPublic())
				i++;
		return i;
	}
	
	public IField[] getPublicFields() {
		IField[] fieldArray = new Field[getPublicFieldCount()];
		int i = 0;
		for (IField field : fields.values())
			if (field.isPublic())
				fieldArray[i++] = field;
		return fieldArray;
	}
	
	public int getPublicMethodCount() {
		int i = 0;
		for (IMethod meth : methods.values())
			if (meth.isPublic())
				i++;
		return i;
	}
	
	public IMethod[] getPublicMethods() {
		IMethod[] methodArray = new Method[getPublicMethodCount()];
		int i = 0;
		for (IMethod meth : methods.values()) {
			if (meth.isPublic())
				methodArray[i++] = meth;
		}
		return methodArray;
	}
	
	public int getProtectedFieldCount() {
		int i = 0;
		for (IField field : fields.values())
			if (field.isProtected())
				i++;
		return i;
	}
	
	public IField[] getProtectedFields() {
		IField[] fieldArray = new Field[getProtectedFieldCount()];
		int i = 0;
		for (IField field : fields.values())
			if (field.isProtected())
				fieldArray[i++] = field;
		return fieldArray;
	}
	
	public int getProtectedMethodCount() {
		int i = 0;
		for (IMethod meth : methods.values())
			if (meth.isProtected())
				i++;
		return i;
	}
	
	public IMethod[] getProtectedMethods() {
		IMethod[] methodArray = new Method[getProtectedMethodCount()];
		int i = 0;
		for (IMethod meth : methods.values()) {
			if (meth.isProtected())
				methodArray[i++] = meth;
		}
		return methodArray;
	}
	
	public int getPrivateFieldCount() {
		int i = 0;
		for (IField field : fields.values())
			if (field.isPrivate())
				i++;
		return i;
	}
	
	public IField[] getPrivateFields() {
		IField[] fieldArray = new Field[getPrivateFieldCount()];
		int i = 0;
		for (IField field : fields.values())
			if (field.isPrivate())
				fieldArray[i++] = field;
		return fieldArray;
	}
	
	public int getPrivateMethodCount() {
		int i = 0;
		for (IMethod meth : methods.values())
			if (meth.isPrivate())
				i++;
		return i;
	}
	
	public IMethod[] getPrivateMethods() {
		IMethod[] methodArray = new Method[getPrivateMethodCount()];
		int i = 0;
		for (IMethod meth : methods.values()) {
			if (meth.isPrivate())
				methodArray[i++] = meth;
		}
		return methodArray;
	}
	
	public int getPackagePrivateFieldCount() {
		int i = 0;
		for (IField field : fields.values())
			if (!field.isPrivate() && !field.isProtected() && !field.isPublic())
				i++;
		return i;
	}
	
	public IField[] getPackagePrivateFields() {
		IField[] fieldArray = new Field[getPackagePrivateFieldCount()];
		int i = 0;
		for (IField field : fields.values())
			if (!field.isPrivate() && !field.isProtected() && !field.isPublic())
				fieldArray[i++] = field;
		return fieldArray;
	}
	
	public int getPackagePrivateMethodCount() {
		int i = 0;
		for (IMethod meth : methods.values())
			if (!meth.isPrivate() && !meth.isProtected() && !meth.isPublic())
				i++;
		return i;
	}
	
	public IMethod[] getPackagePrivateMethods() {
		IMethod[] methodArray = new Method[getPrivateMethodCount()];
		int i = 0;
		for (IMethod meth : methods.values()) {
			if (!meth.isPrivate() && !meth.isProtected() && !meth.isPublic())
				methodArray[i++] = meth;
		}
		return methodArray;
	}
	
	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.jakprojectmodel.IClass#getNumberOfAvailibleFields()
	 */
	public int getAvailableFieldCount() {
		int i = 0;
		for (IField field : fields.values())
			if (field.isAvailable(currentJakfile))
				i++;
		return i;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.jakprojectmodel.IClass#getAvailibleFields()
	 */
	public IField[] getAvailableFields() {
		IField[] fieldArray = new Field[getAvailableFieldCount()];
		int i = 0;
		for (IField field : fields.values())
			if (field.isAvailable(currentJakfile))
				fieldArray[i++] = field;
		return fieldArray;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.jakprojectmodel.IClass#getNumberOfAvailibleMethods()
	 */
	public int getAvailableMethodCount() {
		int i = 0;
		for (IMethod meth : methods.values())
			if (meth.isAvailable(currentJakfile))
				i++;
		return i;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.jakprojectmodel.IClass#getAvailibleMethods()
	 */
	public IMethod[] getAvailableMethods() {
		IMethod[] methodArray = new Method[getAvailableMethodCount()];
		int i = 0;
		for (IMethod meth : methods.values()) {
			if (meth.isAvailable(currentJakfile))
				methodArray[i++] = meth;
		}
		return methodArray;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.jakprojectmodel.IClass#getNumberOfOwnFields()
	 */
	public int getOwnFieldCount() {
		int i = 0;
		for (IField field : fields.values())
			if (field.isOwn(currentJakfile))
				i++;
		return i;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.jakprojectmodel.IClass#getOwnFields()
	 */
	public IField[] getOwnFields() {
		IField[] fieldArray = new Field[getOwnFieldCount()];
		int i = 0;
		for (IField field : fields.values())
			if (field.isOwn(currentJakfile))
				fieldArray[i++] = field;
		return fieldArray;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.jakprojectmodel.IClass#getNumberOfOwnMethods()
	 */
	public int getOwnMethodCount() {
		int i = 0;
		for (IMethod meth : methods.values())
			if (meth.isOwn(currentJakfile))
				i++;
		return i;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.jakprojectmodel.IClass#getOwnMethods()
	 */
	public IMethod[] getOwnMethods() {
		IMethod[] methodArray = new Method[getOwnMethodCount()];
		int i = 0;
		for (IMethod meth : methods.values()) {
			if (meth.isOwn(currentJakfile))
				methodArray[i++] = meth;
		}
		return methodArray;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.core.jakprojectmodel.IClass#setJakfile(org.eclipse.core.resources
	 * .IFile)
	 */
	public void setJakfile(IFile jakfile) {
		currentJakfile = jakfile;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.jakprojectmodel.IClass#getJakfile()
	 */
	public IFile getJakfile() {
		return currentJakfile;
	}

	public String getName() {
		return className;
	}

	public IJakModelElement[] getChildren() {
		IJakModelElement[] elements = new IJakModelElement[getOwnFieldCount()
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

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.jakprojectmodel.IClass#getSources()
	 */
	public LinkedList<IFile> getSources() {
		return sources;
	}
}
