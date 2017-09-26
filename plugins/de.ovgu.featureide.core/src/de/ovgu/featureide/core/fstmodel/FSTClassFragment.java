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

import java.util.HashSet;
import java.util.TreeSet;

import javax.annotation.Nonnull;

/**
 * Collection of the members and characteristics of a class representing by one {@link FSTRole}
 *
 * @author Sebastian Krieter
 */
public class FSTClassFragment extends RoleElement<FSTClassFragment> {

	protected final TreeSet<FSTMethod> methods = new TreeSet<FSTMethod>();
	protected final TreeSet<FSTField> fields = new TreeSet<FSTField>();
	protected final TreeSet<FSTClassFragment> innerClasses = new TreeSet<FSTClassFragment>();
	protected final TreeSet<FSTInvariant> invariants = new TreeSet<FSTInvariant>();

	protected String pckg = null;

	protected boolean innerClass = false;

	protected final HashSet<String> importList = new HashSet<String>(), extendList = new HashSet<String>(), implementList = new HashSet<String>();

	public FSTClassFragment(String name) {
		super(name, null, null, "", -1, -1);
	}

	@Override
	public String getFullName() {
		final StringBuilder fullname = new StringBuilder();
		fullname.append(name);
		fullname.append(" : " + type);
		return fullname.toString();
	}

	public String getPackage() {
		return pckg;
	}

	@Nonnull
	public HashSet<String> getImports() {
		return importList;
	}

	@Nonnull
	public HashSet<String> getExtends() {
		return extendList;
	}

	@Nonnull
	public HashSet<String> getImplements() {
		return implementList;
	}

	@Nonnull
	public TreeSet<FSTField> getFields() {
		return fields;
	}

	@Nonnull
	public TreeSet<FSTInvariant> getInvariants() {
		return invariants;
	}

	@Nonnull
	public TreeSet<FSTMethod> getMethods() {
		return methods;
	}

	@Nonnull
	public TreeSet<FSTClassFragment> getInnerClasses() {
		return innerClasses;
	}

	public boolean add(IRoleElement element) {
		if (element instanceof FSTMethod) {
			if (methods.contains(element)) {
				return false;
			}
			methods.add((FSTMethod) element);
		} else if (element instanceof FSTField) {
			if (fields.contains(element)) {
				return false;
			}
			fields.add((FSTField) element);
		} else if (element instanceof FSTClassFragment) {
			if (innerClasses.contains(element)) {
				return false;
			}
			innerClasses.add((FSTClassFragment) element);
		} else if (element instanceof FSTInvariant) {
			if (invariants.contains(element)) {
				return false;
			}
			invariants.add((FSTInvariant) element);
		} else {
			return false;
		}
		element.setRole(role);
		element.setParent(this);
		return true;
	}

	public void addImport(String imp) {
		importList.add(imp);
	}

	public void addExtend(String extend) {
		extendList.add(extend);
	}

	public void addImplement(String implement) {
		implementList.add(implement);
	}

	public void setPackage(String pckg) {
		this.pckg = pckg;
	}

	public void setType(String type) {
		this.type = type;
	}

	public void setModifiers(String modifiers) {
		this.modifiers = modifiers;
	}

	public boolean isInnerClass() {
		return innerClass;
	}

	public void setInnerClass(boolean innerClass) {
		this.innerClass = innerClass;
	}

}
