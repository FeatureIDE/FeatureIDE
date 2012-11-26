/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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

import java.util.LinkedList;

/**
 * Representation of a method at a role.
 * 
 * @author Jens Meinicke
 */
public class FSTMethod extends RoleElement {

	private LinkedList<String> parameterTypes;
	private boolean isConstructor;
	private boolean refines;

	public FSTMethod(String name, LinkedList<String> parameterTypes,
			String type, String modifiers) {
		this(name, parameterTypes, type, modifiers, -1);
	}
	
	public FSTMethod(String name, LinkedList<String> parameterTypes, String type,
			String modifiers, int beginLine) {
		this(name, parameterTypes, type, modifiers, "", beginLine, -1);
	}
	
	public FSTMethod(String name, LinkedList<String> parameterTypes,
			String type, String modifiers, String body, int beginLine,
			int endLine) {
		super(name, type, modifiers, body, beginLine, endLine);
		this.parameterTypes = parameterTypes;
	}

	@Override
	public String getFullName() {
		StringBuilder name = new StringBuilder();
		name.append(super.name);
		name.append("(");
		for (int i = 0; i < parameterTypes.size(); i++) {
			if (i > 0)
				name.append(", ");
			name.append(parameterTypes.get(i));
		}
		name.append(")");
		if (!"void".equals(type))
			name.append(" : " + type);
		return name.toString();
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

}
