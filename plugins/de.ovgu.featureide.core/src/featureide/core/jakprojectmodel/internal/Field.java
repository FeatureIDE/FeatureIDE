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
package featureide.core.jakprojectmodel.internal;

import java.util.HashMap;
import java.util.HashSet;

import org.eclipse.core.resources.IFile;

import featureide.core.jakprojectmodel.IField;
import featureide.core.jakprojectmodel.IJakElement;

/**
 * @author Tom Brosch
 */
@SuppressWarnings("unchecked")
public class Field extends JakElement implements Comparable, IField {

	
	private String fieldName;
	private String typeName;
	private int dimension;
	
	private HashSet<IFile> ownFiles;
	private HashSet<IFile> availibleFiles;
	private HashMap<IFile, Integer> lineNumbers;
	
	public Field(String fieldName, String typeName, int dim) {
		this.fieldName = fieldName;
		this.typeName = typeName;
		this.dimension = dim;
		
		this.ownFiles = new HashSet<IFile>();
		this.availibleFiles = new HashSet<IFile>();
		this.lineNumbers = new HashMap<IFile, Integer>();
	}
	
	public String getName() {
		String name = fieldName + " : " + typeName;
		for( int i = 0; i < dimension; i++ )
			name += "[]";
		return name;
	}
	
	public IJakElement[] getChildren() {
		return null;
	}
	
	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IField#getIdentifier()
	 */
	public String getIdentifier() {
		return (typeName!=null?typeName:"")+(fieldName!=null?fieldName:"");
	}

	public int compareTo(Object arg0) {
		IField field = (IField)arg0;
		return getIdentifier().compareTo(field.getIdentifier());
	}
	
	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IField#setOwn(org.eclipse.core.resources.IFile)
	 */
	public void setOwn(IFile file) {
		ownFiles.add(file);
	}
	
	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IField#isOwn(org.eclipse.core.resources.IFile)
	 */
	public boolean isOwn(IFile file) {
		return ownFiles.contains(file);
	}
	
	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IField#setAvailible(org.eclipse.core.resources.IFile)
	 */
	public void setAvailible(IFile file) {
		availibleFiles.add(file);
	}
	
	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IField#isAvailible(org.eclipse.core.resources.IFile)
	 */
	public boolean isAvailible(IFile file) {
		return availibleFiles.contains(file);
	}
	
	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IField#setLineNumber(org.eclipse.core.resources.IFile, int)
	 */
	public void setLineNumber(IFile file, int lineNumber) {
		if( lineNumbers.containsKey(file) )
			lineNumbers.remove(file);
		lineNumbers.put(file, lineNumber);
	}
	
	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IField#getLineNumber(org.eclipse.core.resources.IFile)
	 */
	public int getLineNumber(IFile file) {
		if( lineNumbers.containsKey(file) )
			return lineNumbers.get(file);
		return -1;
	}
}
