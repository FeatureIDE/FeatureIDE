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
	
//	public JavaMethodSignature(JavaMethodSignature orgSig) {
//		super(orgSig, false);
//	}
//	
//	private JavaMethodSignature(JavaMethodSignature orgSig, boolean ext) {
//		super(orgSig, ext);
//	}

	@Override
	public String toString() {
		final StringBuilder methodString = new StringBuilder();
		
		methodString.append(super.toString());
		methodString.append(LINE_SEPARATOR);
		
		if (modifiers.length > 0) {
			for (String modifier : modifiers) {
				methodString.append(modifier);
				methodString.append(' ');
			}
		}
		
		if (!isConstructor) {
			methodString.append(type);
			methodString.append(' ');
		}
		
		methodString.append(name);
		methodString.append('(');
		for (int i = 0; i < parameterTypes.size(); i++) {
			if (i > 0) methodString.append(", ");
			methodString.append(parameterTypes.get(i));
			methodString.append(" arg");
			methodString.append(i);
		}
		methodString.append(')');
		
		return methodString.toString();
	}

//	@Override
//	public JavaMethodSignature createExtendedSignature() {
//		return new JavaMethodSignature(this, true);
//	}
}
