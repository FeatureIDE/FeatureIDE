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

import java.util.HashMap;
import java.util.HashSet;

import org.eclipse.core.resources.IFile;

/**
 * @author Tom Brosch
 */
public class FSTField extends FSTModelElement implements Comparable<Object> {

	private String fieldName;
	private String typeName;
	private String modifiers;
	private int dimension;

	private HashSet<IFile> ownFiles;
	private HashSet<IFile> availableFiles;
	private HashMap<IFile, Integer> lineNumbers;

	private String body;
	private int beginLine;
	private int endLine;
	private int composedLine;

	public FSTField(String fieldName, String typeName, int dim, String modifiers) {
		this.fieldName = fieldName;
		this.typeName = typeName;
		this.dimension = dim;
		this.modifiers = modifiers;

		this.ownFiles = new HashSet<IFile>();
		this.availableFiles = new HashSet<IFile>();
		this.lineNumbers = new HashMap<IFile, Integer>();
	}

	public FSTField(String fieldName, String typeName, int dim, String modifiers, String body, int beginLine, int endLine) {
		this.fieldName = fieldName;
		this.typeName = typeName;
		this.dimension = dim;
		this.modifiers = modifiers;

		this.ownFiles = new HashSet<IFile>();
		this.availableFiles = new HashSet<IFile>();
		this.lineNumbers = new HashMap<IFile, Integer>();
		
		this.body = body;
		this.beginLine = beginLine;
		this.endLine = endLine;
	}


	public String getName() {
		StringBuilder name = new StringBuilder();
		name.append(fieldName + " : " + typeName);
		for (int i = 0; i < dimension; i++)
			name.append("[]");
		return name.toString();
	}
	
	public String getOnlyName() {
		return this.fieldName;
	}

	public FSTModelElement[] getChildren() {
		return new FSTModelElement[0];
	}

	public String getIdentifier() {
		return (typeName != null ? typeName : "")
				+ (fieldName != null ? fieldName : "");
	}

	public int compareTo(Object arg0) {
		FSTField field = (FSTField) arg0;
		return getIdentifier().compareTo(field.getIdentifier());
	}

	public void setOwn(IFile file) {
		ownFiles.add(file);
	}

	public boolean isOwn(IFile file) {
		return ownFiles.contains(file);
	}

	public IFile getOwnFile() {
		for (IFile f : ownFiles) {
			return f;
		}
		return null;
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
		return beginLine;
	}

	
	public String getFieldName() {
		return fieldName;
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

	public void setComposedLine(int composedLine) {
		this.composedLine = composedLine;
	}
	
	public int getComposedLine() {
		return composedLine;
	}
	
	public int getBeginLine() {
		return beginLine;
	}
	
	public int getEndLine() {
		return endLine;
	}
	
	public String getBody() {
		return body;
	}

	public FSTField copy() {
		FSTField f = new FSTField(fieldName, typeName, dimension, modifiers, body, beginLine, endLine);
		for (IFile file : ownFiles) {
			f.setOwn(file);
		}
		for (IFile file : availableFiles) {
			f.setAvailable(file);
		}
		for (IFile key : lineNumbers.keySet()) {
			f.setLineNumber(key, lineNumbers.get(key));
		}
		f.setComposedLine(composedLine);
		return f;
	}
}
