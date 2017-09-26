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

import java.util.LinkedList;
import java.util.TreeSet;

import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;

/**
 * Representation of a method at a role.
 *
 * @author Jens Meinicke
 */
public class FSTMethod extends RoleElement<FSTMethod> {

	private final LinkedList<String> parameterTypes;
	private boolean isConstructor;
	private boolean refines;
	private final String contract;
	private final String compKey;
	private int startLineOfContract;
	private final TreeSet<FSTDirective> directives = new TreeSet<FSTDirective>();

	@Override
	public void add(FSTDirective directive) {
		directives.add(directive);
		directive.setRole(super.role);
	}

	@Override
	public TreeSet<FSTDirective> getFSTDirectives() {
		return directives;
	}

	public int getStartLineOfContract() {
		return startLineOfContract;
	}

	/**
	 * @return the contract
	 */
	public String getContract() {
		return contract;
	}

	/**
	 * @return the contract composition technique
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

	public FSTMethod(String name, LinkedList<String> parameterTypes, String type, String modifiers, String body, int beginLine, int endLine, String contract) {
		this(name, parameterTypes, type, modifiers, body, beginLine, endLine, contract, "");
	}

	public FSTMethod(String name, LinkedList<String> parameterTypes, String type, String modifiers, String body, int beginLine, int endLine, String contract,
			String compKey) {
		this(name, parameterTypes, type, modifiers, body, beginLine, endLine, contract, "", -1);
	}

	public FSTMethod(String name, LinkedList<String> parameterTypes, String type, String modifiers, String body, int beginLine, int endLine, String contract,
			String compKey, int startLineOfContract) {
		super(name, type, modifiers, body, beginLine, endLine);
		this.parameterTypes = parameterTypes;
		this.contract = contract;
		this.compKey = compKey;
		if (startLineOfContract > -1) {
			this.startLineOfContract = startLineOfContract;
		}
	}

	@Override
	public String getFullName() {
		final StringBuilder fullname = new StringBuilder();
		fullname.append(name);
		fullname.append("(");
		for (int i = 0; i < parameterTypes.size(); i++) {
			if (i > 0) {
				fullname.append(", ");
			}
			fullname.append(parameterTypes.get(i));
		}
		fullname.append(")");
		if (!"void".equals(type)) {
			fullname.append(" : " + type);
		}
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
		return !contract.isEmpty();
	}

	@Override
	public void setRole(FSTRole parent) {
		super.setRole(parent);
		if (hasContract()) {
			getRole().getFeature().setMethodContracts(true);
		}
	}

	/**
	 *
	 * @return <code>true</code> if an equivalent method exists in an other role of the same class.
	 */
	public boolean inRefinementGroup() {
		for (final FSTRole role : getRole().getFSTClass().getRoles()) {
			if (role.getFeature().equals(getRole().getFeature())) {
				continue;
			}
			for (final FSTMethod method : role.getClassFragment().getMethods()) {
				if (method.getName().equals(getName()) && method.getParameter().equals(getParameter())) {
					return true;
				}
			}
		}
		return false;
	}

	public boolean contractsInRefinements() {
		for (final FSTRole role : getRole().getFSTClass().getRoles()) {
			if (role.getFeature().equals(getRole().getFeature())) {
				continue;
			}
			for (final FSTMethod method : role.getClassFragment().getMethods()) {
				if (method.getName().equals(getName()) && method.getParameter().equals(getParameter()) && method.hasContract()) {
					return true;
				}
			}
		}
		return false;
	}

}
