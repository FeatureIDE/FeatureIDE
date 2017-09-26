/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.core.fstmodel;

import java.util.TreeSet;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;

/**
 * Default implementation of {@link FSTMethod} and {@link FSTField}.
 *
 * @author Jens Meinicke
 */
public abstract class RoleElement<T extends RoleElement<T>> implements Comparable<T>, IRoleElement {

	public final static String DEFAULT_PACKAGE = "(default package).";

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

	protected IRoleElement parent;

	private final TreeSet<FSTDirective> directives = new TreeSet<FSTDirective>();

	public void add(FSTDirective directive) {
		directives.add(directive);
		directive.setRole(role);
	}

	public TreeSet<FSTDirective> getFSTDirectives() {
		return directives;
	}

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

	@Override
	public FSTRole getRole() {
		return role;
	}

	@Override
	public void setRole(FSTRole parent) {
		this.role = parent;
	}

	@Override
	public IRoleElement getParent() {
		return parent;
	}

	private static String removeExtension(String name) {
		final int extIndex = name.lastIndexOf('.');
		return (extIndex > -1) ? name.substring(0, extIndex) : name;
	}

	@Override
	public String getFullIdentifier() {
		final StringBuilder sb = new StringBuilder(removeExtension(name));
		String packageName = (this instanceof FSTClassFragment) ? ((FSTClassFragment) this).getPackage() : null;
		IRoleElement nextParent = parent;
		while (nextParent != null) {
			sb.insert(0, '.');
			if (nextParent.getParent() == null) {
				packageName = ((FSTClassFragment) nextParent).getPackage();
				sb.insert(0, removeExtension(nextParent.getName()));
			} else {
				sb.insert(0, nextParent.getName());
			}
			nextParent = nextParent.getParent();
		}
		final String className = sb.toString();
		return ((packageName == null) ? DEFAULT_PACKAGE : packageName + ".") + className.substring(className.lastIndexOf('/') + 1);
	}

	@Override
	public void setParent(IRoleElement parent) {
		this.parent = parent;
	}

	public IFile getFile() {
		return role.getFile();
	}

	public int getLine() {
		return beginLine;
	}

	public void setLine(int lineNumber) {
		this.beginLine = lineNumber;
	}

	public void setEndLine(int lineNumber) {
		this.endLine = lineNumber;
	}

	public int getEndLine() {
		return endLine;
	}

	public int getMethodLength() {
		return endLine - beginLine;
	}

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

	public String getType() {
		return type;
	}

	@Override
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
	 * @return <code>true</code> if the given element is equivalent in its structure and it has the same class as this element
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = (prime * result) + ((getFullName() == null) ? 0 : getFullName().hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if ((obj == null) || !obj.getClass().equals(this.getClass())) {
			return false;
		}
		final IRoleElement other = (IRoleElement) obj;
		if (!other.getFullName().equals(getFullName())) {
			return false;
		}

		return true;
	}

	@Override
	public String getJavaDocComment() {
		return javaDocComment;
	}

	@Override
	public void setJavaDocComment(String javaDocComment) {
		this.javaDocComment = javaDocComment;
	}

	@Override
	public int compareTo(T element) {
		if (this == element) {
			return 0;
		}
		return getFullName().compareToIgnoreCase(element.getFullName());
	}

}
