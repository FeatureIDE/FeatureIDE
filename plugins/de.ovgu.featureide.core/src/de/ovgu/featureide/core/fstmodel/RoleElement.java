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
package de.ovgu.featureide.core.fstmodel;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.signature.abstr.AbstractSignature;

/**
 * Default implementation of {@link FSTMethod} and {@link FSTField}.
 * 
 * @author Jens Meinicke
 */
public abstract class RoleElement<T extends RoleElement<T>> implements Comparable<T>, IRoleElement{

	private static final String STATIC = "static";
	private static final String PUBLIC = "public";
	private static final String PROTECTED = "protected";
	private static final String PRIVATE = "private";
	private static final String FINAL = "final";

	protected String name;
	protected String type;
	protected String modifiers;
	protected String body;
	protected String javaDocComment = null;
	protected int beginLine;
	protected int endLine;
	protected int composedLine;

	protected FSTRole role;
	
	protected AbstractSignature signature;

	public RoleElement(String name, String type, String modifiers) {
		this(name, type, modifiers, "", -1, -1);
	}

	public RoleElement(String name, String type, String modifiers, String body, int beginLine, int endLine) {
		this.name = name;
		this.type = type;
		this.modifiers = modifiers;
		this.body = body;
		this.beginLine = beginLine;
		this.endLine = endLine;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.fstmodel.IRoleElement#getRole()
	 */
	public FSTRole getRole() {
		return role;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.fstmodel.IRoleElement#setRole(de.ovgu.featureide.core.fstmodel.FSTRole)
	 */
	public void setRole(FSTRole parent) {
		this.role = parent;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.fstmodel.IRoleElement#getFile()
	 */
	public IFile getFile() {
		return role.getFile();
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.fstmodel.IRoleElement#getLine()
	 */
	public int getLine() {
		return beginLine;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.fstmodel.IRoleElement#setLine(int)
	 */
	public void setLine(int lineNumber) {
		this.beginLine = lineNumber;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.fstmodel.IRoleElement#getEndLine()
	 */
	public int getEndLine() {
		return endLine;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.fstmodel.IRoleElement#getComposedLine()
	 */
	public int getComposedLine() {
		return composedLine;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.fstmodel.IRoleElement#setComposedLine(int)
	 */
	public void setComposedLine(int line) {
		composedLine = line;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.fstmodel.IRoleElement#getBody()
	 */
	public String getBody() {
		return body;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.fstmodel.IRoleElement#isFinal()
	 */
	public boolean isFinal() {
		return modifiers.contains(FINAL);
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.fstmodel.IRoleElement#isPrivate()
	 */
	public boolean isPrivate() {
		return modifiers.contains(PRIVATE);
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.fstmodel.IRoleElement#isProtected()
	 */
	public boolean isProtected() {
		return modifiers.contains(PROTECTED);
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.fstmodel.IRoleElement#isPublic()
	 */
	public boolean isPublic() {
		return modifiers.contains(PUBLIC);
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.fstmodel.IRoleElement#isStatic()
	 */
	public boolean isStatic() {
		return modifiers.contains(STATIC);
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.fstmodel.IRoleElement#getType()
	 */
	public String getType() {
		return type;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.fstmodel.IRoleElement#getName()
	 */
	public String getName() {
		return name;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.fstmodel.IRoleElement#getModifiers()
	 */
	public String getModifiers() {
		return modifiers;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.fstmodel.IRoleElement#toString()
	 */
	@Override
	public String toString() {
		return getName();
	}


	/**
	 * @return
	 * 		<code>true</code> if the given element is equivalent
	 * 		in its structure and it has the same class as this element
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		return result;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (!(obj instanceof IRoleElement))
			return false;
		IRoleElement other = (IRoleElement) obj;
		if (!other.getClass().equals(this.getClass()))
			return false;
	
		if (!other.getFullName().equals(this.getFullName()))
			return false;
		
		
		return true;
	}
	
/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.fstmodel.IRoleElement#getJavaDocComment()
	 */
	public String getJavaDocComment() {
		return javaDocComment;

	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.fstmodel.IRoleElement#setJavaDocComment(java.lang.String)
	 */
	public void setJavaDocComment(String javaDocComment) {
		this.javaDocComment = javaDocComment;
	}
	
	/*
	 * default implementation
	 * */
	public int compareTo(T element) {
	
		if(this == element)
			return 0;
		
		return this.getFullName().compareToIgnoreCase(element.getFullName());
	}
		
		
	

}
