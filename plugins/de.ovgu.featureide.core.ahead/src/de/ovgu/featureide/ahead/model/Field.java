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

import java.util.HashMap;
import java.util.HashSet;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.fstmodel.IFSTModelElement;
import de.ovgu.featureide.core.fstmodel.IField;


/**
 * @author Tom Brosch
 */
public class Field extends JakModelElement implements Comparable<Object>, IField {

	private String fieldName;
	private String typeName;
	private String modifiers;
	private int dimension;

	private HashSet<IFile> ownFiles;
	private HashSet<IFile> availableFiles;
	private HashMap<IFile, Integer> lineNumbers;

	public Field(String fieldName, String typeName, int dim, String modifiers) {
		this.fieldName = fieldName;
		this.typeName = typeName;
		this.dimension = dim;
		this.modifiers = modifiers;

		this.ownFiles = new HashSet<IFile>();
		this.availableFiles = new HashSet<IFile>();
		this.lineNumbers = new HashMap<IFile, Integer>();
	}

	public String getName() {
		String name = fieldName + " : " + typeName;
		for (int i = 0; i < dimension; i++)
			name += "[]";
		return name;
	}

	public IFSTModelElement[] getChildren() {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.jakprojectmodel.IField#getIdentifier()
	 */
	public String getIdentifier() {
		return (typeName != null ? typeName : "")
				+ (fieldName != null ? fieldName : "");
	}

	public int compareTo(Object arg0) {
		IField field = (IField) arg0;
		return getIdentifier().compareTo(field.getIdentifier());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.core.jakprojectmodel.IField#setOwn(org.eclipse.core.resources
	 * .IFile)
	 */
	public void setOwn(IFile file) {
		ownFiles.add(file);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.core.jakprojectmodel.IField#isOwn(org.eclipse.core.resources
	 * .IFile)
	 */
	public boolean isOwn(IFile file) {
		return ownFiles.contains(file);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.core.jakprojectmodel.IField#setAvailible(org.eclipse.core.
	 * resources.IFile)
	 */
	public void setAvailable(IFile file) {
		availableFiles.add(file);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.core.jakprojectmodel.IField#isAvailible(org.eclipse.core.resources
	 * .IFile)
	 */
	public boolean isAvailable(IFile file) {
		return availableFiles.contains(file);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.core.jakprojectmodel.IField#setLineNumber(org.eclipse.core
	 * .resources.IFile, int)
	 */
	public void setLineNumber(IFile file, int lineNumber) {
		if (lineNumbers.containsKey(file))
			lineNumbers.remove(file);
		lineNumbers.put(file, lineNumber);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.core.jakprojectmodel.IField#getLineNumber(org.eclipse.core
	 * .resources.IFile)
	 */
	public int getLineNumber(IFile file) {
		if (lineNumbers.containsKey(file))
			return lineNumbers.get(file);
		return -1;
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
}
