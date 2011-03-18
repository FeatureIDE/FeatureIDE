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
package de.ovgu.featureide.core.fstmodel;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;



/**
 * @author Tom Brosch
 */
public class FSTMethod extends FSTModelElement implements Comparable<Object> {

	private String methodName;
	private LinkedList<String> parameterTypes;
	private String returnType;
	private String modifiers;
	private HashSet<IFile> ownFiles;
	private HashSet<IFile> availableFiles;
	private HashMap<IFile, Integer> lineNumbers;

	public FSTMethod() {
		this(null, null, null,null);
	}

	public FSTMethod(String methodName, LinkedList<String> parameterTypes,
			String returnType, String modifiers) {
		this.methodName = methodName;
		this.parameterTypes = parameterTypes;
		this.returnType = returnType;
		this.ownFiles = new HashSet<IFile>();
		this.availableFiles = new HashSet<IFile>();
		this.lineNumbers = new HashMap<IFile, Integer>();
		this.modifiers = modifiers;
	}

	public String getName() {
		String name = methodName + "(";
		for (int i = 0; i < parameterTypes.size(); i++) {
			if (i > 0)
				name += ", ";
			name += parameterTypes.get(i);
		}
		name += ")";
		if (!returnType.equals("void"))
			name += " : " + returnType;
		return name;
	}

	public String getMethodName() {
		return methodName;
	}

	public FSTModelElement[] getChildren() {
		return null;
	}

	public String getIdentifier() {
		String id = (returnType != null ? returnType : "")
				+ (methodName != null ? methodName : "");
		if (parameterTypes != null)
			for (String type : parameterTypes)
				id += type;
		return id;
	}

	public int compareTo(Object arg0) {
		FSTMethod meth = (FSTMethod) arg0;
		return getIdentifier().compareTo(meth.getIdentifier());
	}

	public void setOwn(IFile file) {
		ownFiles.add(file);
	}

	public boolean isOwn(IFile file) {
		return ownFiles.contains(file);
	}

	public void setAvailable(IFile file) {
		availableFiles.add(file);
	}

	public boolean isAvailable(IFile file) {
		return availableFiles.contains(file);
	}

	public void setLineNumber(IFile file, int lineNumber) {
		if (lineNumbers.containsKey(file))
			lineNumbers.remove(file);
		lineNumbers.put(file, lineNumber);
	}

	public int getLineNumber(IFile file) {
		if (lineNumbers.containsKey(file))
			return lineNumbers.get(file);
		return -1;
	}

	public boolean isFinal() {
		return modifiers.contains("final");
	}

	public boolean isPrivate() {
		return modifiers.contains("private");
	}

	public boolean isProtected() {
		return modifiers.contains("protected");
	}

	public boolean isPublic() {
		return modifiers.contains("public");
	}

	public boolean isStatic() {
		return modifiers.contains("static");
	}
}
