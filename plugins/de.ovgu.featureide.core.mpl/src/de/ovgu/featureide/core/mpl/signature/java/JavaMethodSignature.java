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

import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractMethodSignature;

/** 
 * Holds the java signature of a method.
 * 
 * @author Sebastian Krieter
 */
public class JavaMethodSignature extends AbstractMethodSignature {
	
	public JavaMethodSignature(AbstractClassSignature parent, String name, String modifier, String type, LinkedList<String> parameterTypes, boolean isConstructor) {
		super(parent, name, modifier, type, parameterTypes, isConstructor);
	}
	
	public JavaMethodSignature(JavaMethodSignature orgSig) {
		super(orgSig, false);
	}
	
	private JavaMethodSignature(JavaMethodSignature orgSig, boolean ext) {
		super(orgSig, ext);
	}

	@Override
	public String toString() {
		StringBuilder signature = new StringBuilder();
		
		signature.append(super.toString());
		signature.append(LINE_SEPARATOR);
		
		if (!modifiers.isEmpty()) {
			signature.append(modifiers);
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
	public JavaMethodSignature createExtendedSignature() {
		return new JavaMethodSignature(this, true);
	}
}
