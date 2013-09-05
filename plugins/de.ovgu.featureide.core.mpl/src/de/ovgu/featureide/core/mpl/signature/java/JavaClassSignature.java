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

/**
 * Holds the java signature of a class.
 * 
 * @author Sebastian Krieter
 */
public class JavaClassSignature extends AbstractClassSignature {
	
	public JavaClassSignature(AbstractClassSignature parent, String name, String modifiers, String type, String pckg) {
		super(parent, name, modifiers, type, pckg);
	}
	
//	public JavaClassSignature(JavaClassSignature orgSig) {
//		this(orgSig, false);
//	}
//	
//	private JavaClassSignature(JavaClassSignature orgSig, boolean ext) {
//		super(orgSig, ext);
//	}
	
	@Override
	public String toString() {		
		StringBuilder sb = new StringBuilder();
		
		sb.append(super.toString());
		sb.append(LINE_SEPARATOR);
		
		if (modifiers.length > 0) {
			for (String modifier : modifiers) {
				sb.append(modifier);
				sb.append(' ');
			}
		}
		sb.append(type);
		sb.append(' ');
		sb.append(name);
		
		return sb.toString();
	}

//	@Override
//	public JavaClassSignature createExtendedSignature() {
//		return new JavaClassSignature(this, true);
//	}
}
