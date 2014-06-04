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

import java.util.HashSet;
import java.util.LinkedList;

import javax.annotation.Nonnull;

/**
 * Collection of the members and characteristics of a class representing by one {@link FSTRole}
 * 
 * @author Sebastian Krieter
 */
public class FSTClassFragment extends RoleElement {
	protected final LinkedList<FSTMethod> methods = new LinkedList<FSTMethod>();
	protected final LinkedList<FSTField> fields = new LinkedList<FSTField>();
	protected final LinkedList<FSTClassFragment> innerClasses = new LinkedList<FSTClassFragment>();
	protected final LinkedList<FSTInvariant> invariants = new LinkedList<FSTInvariant>();

	
	protected String pckg = null;

	protected final HashSet<String> 
		importList = new HashSet<String>(),
		extendList = new HashSet<String>(),
		implementList = new HashSet<String>();

	public FSTClassFragment(String name) {
		super(name, null, null, "", -1, -1);
	}

	@Override
	public String getFullName() {
		StringBuilder fullname = new StringBuilder();
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
	public LinkedList<FSTField> getFields() {
		return fields;
	}

	@Nonnull
	public LinkedList<FSTInvariant> getInvariants() {
		return invariants;
	}
	
	@Nonnull
	public LinkedList<FSTMethod> getMethods() {
		return methods;
	}
	
	@Nonnull
	public LinkedList<FSTClassFragment> getInnerClasses() {
		return innerClasses;
	}
	

	
	public boolean add(RoleElement element) {
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
		} else if(element instanceof FSTClassFragment) {
			if (innerClasses.contains(element)) {
				return false;
			}
			innerClasses.add((FSTClassFragment) element);
		} else if(element instanceof FSTInvariant) {
			if (invariants.contains(element)) {
				return false;
			}
			invariants.add((FSTInvariant) element);
		}  else {
			return false;
		}
		element.setRole(role);
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
}
