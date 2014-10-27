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

import java.util.LinkedList;

/**
 * Representation of a method at a role.
 * 
 * @author Jens Meinicke
 */
public class FSTMethod extends RoleElement<FSTMethod> {

	private LinkedList<String> parameterTypes;
	private boolean isConstructor;
	private boolean refines;
	private String contract;

	/**
	 * @return the contract
	 */
	public String getContract() {
		return contract;
	}

	private String compKey;

	/**
	 * @return the compKey
	 */
	public String getCompKey() {
		return compKey;
	}

	public FSTMethod(String name, LinkedList<String> parameterTypes, String type, String modifiers) {
		this(name, parameterTypes, type, modifiers, -1);
	}

	public FSTMethod(String name, LinkedList<String> parameterTypes, String type, String modifiers, int beginLine) {
		this(name, parameterTypes, type, modifiers, "", beginLine, -1);
	}

	public FSTMethod(String name, LinkedList<String> parameterTypes, String type, String modifiers, String body, int beginLine, int endLine) {
		this(name, parameterTypes, type, modifiers, body, beginLine, endLine, "", "");
	}

	public FSTMethod(String name, LinkedList<String> parameterTypes, String type, String modifiers, String body, int beginLine,
			int endLine, String contract) {
		this(name, parameterTypes, type, modifiers, body, beginLine, endLine, contract, "");
	}

	public FSTMethod(String name, LinkedList<String> parameterTypes, String type, String modifiers, String body, int beginLine,
			int endLine, String contract, String compKey) {
		super(name, type, modifiers, body, beginLine, endLine);
		this.parameterTypes = parameterTypes;
		this.contract = contract;
		this.compKey = compKey;
	}

	public String getFullName() {
		StringBuilder fullname = new StringBuilder();
		fullname.append(name);
		fullname.append("(");
		for (int i = 0; i < parameterTypes.size(); i++) {
			if (i > 0)
				fullname.append(", ");
			fullname.append(parameterTypes.get(i));
		}
		fullname.append(")");
		if (!"void".equals(type))
			fullname.append(" : " + type);
		return fullname.toString();
	}

	public boolean isConstructor() {
		return isConstructor;
	}

	public void setConstructor(boolean isConstructor) {
		this.isConstructor = isConstructor;
	}

	public boolean refines() {
		return refines;
	}

	public void setRefines(boolean refines) {
		this.refines = refines;
	}

	public LinkedList<String> getParameter() {
		return parameterTypes;
	}

	public boolean hasContract() {
		return contract.length() > 0;
	}

	/**
	 * 
	 * @return <code>true</code> if an equivalent method exists in an other role
	 *         of the same class.
	 */
	public boolean inRefinementGroup() {
		for (FSTRole role : getRole().getFSTClass().getRoles()) {
			if (role.getFeature().equals(getRole().getFeature())) {
				continue;
			}
			for (FSTMethod method : role.getClassFragment().getMethods()) {
				if (method.getName().equals(getName()) && method.getParameter().equals(getParameter())) {
					return true;
				}
			}
		}
		return false;
	}

	public boolean contractsInRefinements() {
		for (FSTRole role : getRole().getFSTClass().getRoles()) {
			if (role.getFeature().equals(getRole().getFeature())) {
				continue;
			}
			for (FSTMethod method : role.getClassFragment().getMethods()) {
				if (method.getName().equals(getName()) && method.getParameter().equals(getParameter()) 
						&& method.hasContract()) {
					return true;
				}
			}
		}
		return false;
	}

}
