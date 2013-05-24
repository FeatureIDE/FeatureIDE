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
package de.ovgu.featureide.core.mpl.signature.java;

import java.util.LinkedList;

import de.ovgu.featureide.core.mpl.signature.AbstractSignature;

/** 
 * Holds the java signature of a method.
 * 
 * @author Sebastian Krieter
 */
public class JavaMethodSignature extends AbstractSignature {

	protected final LinkedList<String> parameterTypes;
	protected final boolean isConstructor;
	
	public JavaMethodSignature(String name, String modifier, String type, LinkedList<String> parameterTypes, boolean isConstructor, boolean ext) {
		super(name, modifier, type, null, ext);
		this.isConstructor = isConstructor;
		this.parameterTypes = new LinkedList<String>(parameterTypes);
	}

	public JavaMethodSignature(JavaMethodSignature curMethod) {
		this(curMethod, false);
	}
	
	private JavaMethodSignature(JavaMethodSignature curMethod, boolean ext) {
		super(curMethod.name, curMethod.modifiers, curMethod.type, curMethod.viewTags, 
				ext || curMethod.ext);
		parameterTypes = curMethod.getParameterTypes();
		isConstructor = curMethod.isConstructor();
	}

	public LinkedList<String> getParameterTypes() {
		return parameterTypes;
	}

	public boolean isConstructor() {
		return isConstructor;
	}

	@Override
	public String toString() {
		StringBuilder signature = new StringBuilder(modifiers);
		if (!modifiers.isEmpty()) {
			signature.append(' ');
		}
		
		if (!isConstructor) {
			signature.append(type);
			signature.append(' ');
		}
		
		signature.append(name);
		signature.append('(');
		for (int i = 0; i < parameterTypes.size(); i++) {
			if (i > 0) signature.append(", ");
			signature.append(parameterTypes.get(i));
			signature.append(" arg");
			signature.append(i);
		}
		signature.append(')');
		
		return signature.toString();
	}

	@Override
	public boolean equals(Object obj) {
		if (!super.equals(obj)) {
			return false;
		}
		
		JavaMethodSignature otherSig = (JavaMethodSignature) obj;
		
		if (isConstructor != otherSig.isConstructor) {
			return false;
		}
		if (parameterTypes.size() != otherSig.parameterTypes.size()) {
			return false;
		}
		for (int i = 0; i < parameterTypes.size(); i++) {
			if (!parameterTypes.get(i).equals(otherSig.parameterTypes.get(i))) {
				return false;
			}
		}
		
		return true;
	}

	@Override
	public int hashCode() {
		StringBuilder signature = new StringBuilder(modifiers);
		
		if (!isConstructor) {
			signature.append(type);
		}
		
		signature.append(name);
		for (int i = 0; i < parameterTypes.size(); i++) {
			signature.append(parameterTypes.get(i));
		}
		
		return signature.toString().hashCode();
	}

	@Override
	public JavaMethodSignature createExtendedSignature() {
		return new JavaMethodSignature(this, true);
	}
}
