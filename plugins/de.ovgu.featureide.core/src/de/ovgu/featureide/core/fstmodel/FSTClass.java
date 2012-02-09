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
package de.ovgu.featureide.core.fstmodel;

import java.util.LinkedList;
import java.util.TreeMap;

import org.eclipse.core.resources.IFile;

/**
 * Describes a class of a featureproject according to a selected configuration
 * 
 * @author Tom Brosch
 * @author Thomas Thuem
 * 
 */
public class FSTClass extends FSTModelElement {

	// Only the own AST methods are implemented

	private IFile currentFile;
	
	private LinkedList<IFile> files = new LinkedList<IFile>();

	private TreeMap<String, FSTMethod> methods;

	private TreeMap<String, FSTField> fields;

	private String className;
	
	private boolean isClassFile = false;

	public FSTClass() {
		this("");
	}
	
	public boolean isClassFile(IFile file) {
		return files.contains(file);
	}
	
	public LinkedList<IFile> getClassFiles() {
		return files;
	}
	
	public void clear() {
		methods.clear();
		fields.clear();
	}

	/**
	 * Creates a new instance of a class
	 * 
	 * @param className
	 *            The name of the class
	 */
	public FSTClass(String className) {
		this.className = className;
		methods = new TreeMap<String, FSTMethod>();
		fields = new TreeMap<String, FSTField>();
	}

	public int getFieldCount() {
		return fields.size();
	}

	public FSTField[] getFields() {
		return fields.values().toArray(new FSTField[fields.values().size()]);
	}

	public int getMethodCount() {
		return methods.size();
	}

	public FSTMethod[] getMethods() {
		FSTMethod[] methodArray = new FSTMethod[methods.size()];
		int i = 0;
		for (FSTMethod meth : methods.values())
			methodArray[i++] = meth;
		return methodArray;
	}

	public int getPublicFieldCount() {
		int i = 0;
		for (FSTField field : fields.values())
			if (field.isPublic())
				i++;
		return i;
	}

	public FSTField[] getPublicFields() {
		FSTField[] fieldArray = new FSTField[getPublicFieldCount()];
		int i = 0;
		for (FSTField field : fields.values())
			if (field.isPublic())
				fieldArray[i++] = field;
		return fieldArray;
	}

	public int getPublicMethodCount() {
		int i = 0;
		for (FSTMethod meth : methods.values())
			if (meth.isPublic())
				i++;
		return i;
	}

	public FSTMethod[] getPublicMethods() {
		FSTMethod[] methodArray = new FSTMethod[getPublicMethodCount()];
		int i = 0;
		for (FSTMethod meth : methods.values()) {
			if (meth.isPublic())
				methodArray[i++] = meth;
		}
		return methodArray;
	}

	public int getProtectedFieldCount() {
		int i = 0;
		for (FSTField field : fields.values())
			if (field.isProtected())
				i++;
		return i;
	}

	public FSTField[] getProtectedFields() {
		FSTField[] fieldArray = new FSTField[getProtectedFieldCount()];
		int i = 0;
		for (FSTField field : fields.values())
			if (field.isProtected())
				fieldArray[i++] = field;
		return fieldArray;
	}

	public int getProtectedMethodCount() {
		int i = 0;
		for (FSTMethod meth : methods.values())
			if (meth.isProtected())
				i++;
		return i;
	}

	public FSTMethod[] getProtectedMethods() {
		FSTMethod[] methodArray = new FSTMethod[getProtectedMethodCount()];
		int i = 0;
		for (FSTMethod meth : methods.values()) {
			if (meth.isProtected())
				methodArray[i++] = meth;
		}
		return methodArray;
	}

	public int getPrivateFieldCount() {
		int i = 0;
		for (FSTField field : fields.values())
			if (field.isPrivate())
				i++;
		return i;
	}

	public FSTField[] getPrivateFields() {
		FSTField[] fieldArray = new FSTField[getPrivateFieldCount()];
		int i = 0;
		for (FSTField field : fields.values())
			if (field.isPrivate())
				fieldArray[i++] = field;
		return fieldArray;
	}

	public int getPrivateMethodCount() {
		int i = 0;
		for (FSTMethod meth : methods.values())
			if (meth.isPrivate())
				i++;
		return i;
	}

	public FSTMethod[] getPrivateMethods() {
		FSTMethod[] methodArray = new FSTMethod[getPrivateMethodCount()];
		int i = 0;
		for (FSTMethod meth : methods.values()) {
			if (meth.isPrivate())
				methodArray[i++] = meth;
		}
		return methodArray;
	}

	public int getPackagePrivateFieldCount() {
		int i = 0;
		for (FSTField field : fields.values())
			if (!field.isPrivate() && !field.isProtected() && !field.isPublic())
				i++;
		return i;
	}

	public FSTField[] getPackagePrivateFields() {
		FSTField[] fieldArray = new FSTField[getPackagePrivateFieldCount()];
		int i = 0;
		for (FSTField field : fields.values())
			if (!field.isPrivate() && !field.isProtected() && !field.isPublic())
				fieldArray[i++] = field;
		return fieldArray;
	}

	public int getPackagePrivateMethodCount() {
		int i = 0;
		for (FSTMethod meth : methods.values())
			if (!meth.isPrivate() && !meth.isProtected() && !meth.isPublic())
				i++;
		return i;
	}

	public FSTMethod[] getPackagePrivateMethods() {
		FSTMethod[] methodArray = new FSTMethod[getPrivateMethodCount()];
		int i = 0;
		for (FSTMethod meth : methods.values()) {
			if (!meth.isPrivate() && !meth.isProtected() && !meth.isPublic())
				methodArray[i++] = meth;
		}
		return methodArray;
	}

	public int getAvailableFieldCount() {
		int i = 0;
		for (FSTField field : fields.values())
			if (field.isAvailable(currentFile))
				i++;
		return i;
	}

	public FSTField[] getAvailableFields() {
		FSTField[] fieldArray = new FSTField[getAvailableFieldCount()];
		int i = 0;
		for (FSTField field : fields.values())
			if (field.isAvailable(currentFile))
				fieldArray[i++] = field;
		return fieldArray;
	}

	public int getAvailableMethodCount() {
		int i = 0;
		for (FSTMethod meth : methods.values())
			if (meth.isAvailable(currentFile))
				i++;
		return i;
	}

	public FSTMethod[] getAvailableMethods() {
		FSTMethod[] methodArray = new FSTMethod[getAvailableMethodCount()];
		int i = 0;
		for (FSTMethod meth : methods.values()) {
			if (meth.isAvailable(currentFile))
				methodArray[i++] = meth;
		}
		return methodArray;
	}

	public int getOwnFieldCount() {
		int i = 0;
		for (FSTField field : fields.values())
			if (field.isOwn(currentFile))
				i++;
		return i;
	}

	public FSTField[] getOwnFields() {
		FSTField[] fieldArray = new FSTField[getOwnFieldCount()];
		int i = 0;
		for (FSTField field : fields.values())
			if (field.isOwn(currentFile))
				fieldArray[i++] = field;
		return fieldArray;
	}

	public int getOwnMethodCount() {
		int i = 0;
		for (FSTMethod meth : methods.values())
			if (meth.isOwn(currentFile))
				i++;
		return i;
	}

	public FSTMethod[] getOwnMethods() {
		FSTMethod[] methodArray = new FSTMethod[getOwnMethodCount()];
		int i = 0;
		for (FSTMethod meth : methods.values()) {
			if (meth.isOwn(currentFile))
				methodArray[i++] = meth;
		}
		return methodArray;
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

	public FSTModelElement[] getChildren() {
		FSTModelElement[] elements = new FSTModelElement[getOwnFieldCount()
				+ getOwnMethodCount()];
		FSTField[] fieldArray = getOwnFields();
		FSTMethod[] methodArray = getOwnMethods();
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

	/**
	 * @param file
	 */
	public void setName(String name) {
		className = name;
	}

	public void setClassFile() {
		this.isClassFile = true;
	}

	public boolean isClassFile() {
		return isClassFile;
	}

	/**
	 * @param source
	 */
	public void addFile(IFile source) {
		if (!files.contains(source)) {
			files.add(source);
		}
		currentFile = source;
	}

	/**
	 * Checks if the class contains the given element.
	 * @param element A Method or Field
	 * @return
	 */
	public boolean contains(FSTModelElement element) {
		if (element instanceof FSTMethod) {
			return methods.containsKey(((FSTMethod)element).getIdentifier());
		} else if (element instanceof FSTField) {
			return fields.containsKey(((FSTField)element).getIdentifier());
		}
		return false;
	}

	/**
	 * Returns the element with the same identifier. 
	 * @param identifier
	 * @return
	 */
	public FSTModelElement get(FSTModelElement element) {
		if (element instanceof FSTMethod) {
			return methods.get(((FSTMethod)element).getIdentifier());
		} else if (element instanceof FSTField) {
			return fields.get(((FSTField)element).getIdentifier());
		}
		return null;
	}

	/**
	 * Removes the given element.
	 * @param identifier
	 */
	public void remove(FSTModelElement element) {
		if (element instanceof FSTMethod) {
			methods.remove(((FSTMethod)element).getIdentifier());
		} else if (element instanceof FSTField) {
			fields.remove(((FSTField)element).getIdentifier());
		}
	}
	
	/**
	 * Adds the given element.
	 * @param element
	 */
	public void add(FSTModelElement element) {
		if (element instanceof FSTMethod) {
			methods.put(((FSTMethod)element).getIdentifier(), (FSTMethod)element);
		} else if (element instanceof FSTField) {
			fields.put(((FSTField)element).getIdentifier(), (FSTField)element);
		}
	}
}
