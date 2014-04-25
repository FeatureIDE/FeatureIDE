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

/**
 * Default implementation of {@link FSTMethod} and {@link FSTField}.
 * 
 * @author Jens Meinicke
 */
public abstract class RoleElement {

	private static final String STATIC = "static";
	private static final String PUBLIC = "public";
	private static final String PROTECTED = "protected";
	private static final String PRIVATE = "private";
	private static final String FINAL = "final";

	protected String name;
	protected String type;
	protected String modifiers;
	protected String body;
	protected String javaDocCommtent = null;
	protected int beginLine;
	protected int endLine;
	protected int composedLine;

	protected FSTRole role;

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

	public FSTRole getRole() {
		return role;
	}

	public void setRole(FSTRole parent) {
		this.role = parent;
	}

	public IFile getFile() {
		return role.getFile();
	}

	/**
	 * 
	 * @return The line of this method at the features file.
	 */
	public int getLine() {
		return beginLine;
	}

	public void setLine(int lineNumber) {
		this.beginLine = lineNumber;
	}

	/**
	 * 
	 * @return The last line of this method at the features file.
	 */
	public int getEndLine() {
		return endLine;
	}

	/**
	 * 
	 * @return The line of this method at the composed file.
	 */
	public int getComposedLine() {
		return composedLine;
	}

	public void setComposedLine(int line) {
		composedLine = line;
	}

	public String getBody() {
		return body;
	}

	public boolean isFinal() {
		return modifiers.contains(FINAL);
	}

	public boolean isPrivate() {
		return modifiers.contains(PRIVATE);
	}

	public boolean isProtected() {
		return modifiers.contains(PROTECTED);
	}

	public boolean isPublic() {
		return modifiers.contains(PUBLIC);
	}

	public boolean isStatic() {
		return modifiers.contains(STATIC);
	}

	public abstract String getFullName();

	public String getType() {
		return type;
	}

	public String getName() {
		return name;
	}

	public String getModifiers() {
		return modifiers;
	}

	@Override
	public String toString() {
		return getName();
	}

	/**
	 * @return <code>true</code> if the given element is equivalent in it's
	 *         structure and it has the same class as this element
	 */
	public boolean comparesTo(RoleElement element) {
		return getFullName().equals(element.getFullName()) && getClass().equals(element.getClass());
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof RoleElement) {
			return comparesTo((RoleElement) obj);
		}
		return false;
	}

	/**
	 * @return the javaDocCommtent
	 */
	public String getJavaDocCommtent() {
		return javaDocCommtent;
	}

	/**
	 * @param javaDocCommtent the javaDocCommtent to set
	 */
	public void setJavaDocCommtent(String javaDocCommtent) {
		this.javaDocCommtent = javaDocCommtent;
	}
}
