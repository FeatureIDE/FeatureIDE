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

import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractFieldSignature;

/** 
 * Holds the java signature of a field.
 * 
 * @author Sebastian Krieter
 */
public class JavaFieldSignature extends AbstractFieldSignature {

	public JavaFieldSignature(AbstractClassSignature parent, String name, String modifiers, String type) {
		super(parent, name, modifiers, type);
	}

//	public JavaFieldSignature(JavaFieldSignature orgSig) {
//		this(orgSig, false);
//	}
//	
//	private JavaFieldSignature(JavaFieldSignature orgSig, boolean ext) {
//		super(orgSig, ext);
//	}

	@Override
	public String toString() {
		StringBuilder signature = new StringBuilder();
		
		signature.append(super.toString());
		signature.append(LINE_SEPARATOR);
		
		if (modifiers.length > 0) {
			for (String modifier : modifiers) {
				signature.append(modifier);
				signature.append(' ');
			}
		}
		signature.append(type);
		signature.append(' ');
		signature.append(name);
		
		return signature.toString();
	}

//	@Override
//	public JavaFieldSignature createExtendedSignature() {
//		return new JavaFieldSignature(this, true);
//	}
}
