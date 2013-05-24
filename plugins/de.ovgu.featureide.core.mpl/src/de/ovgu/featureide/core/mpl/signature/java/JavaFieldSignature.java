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

import de.ovgu.featureide.core.mpl.signature.AbstractSignature;

/** 
 * Holds the java signature of a field.
 * 
 * @author Sebastian Krieter
 */
public class JavaFieldSignature extends AbstractSignature {

	public JavaFieldSignature(String name, String modifiers, String type) {
		super(name, modifiers, type, null, false);
	}

	public JavaFieldSignature(JavaFieldSignature curField) {
		this(curField, false);
	}
	
	private JavaFieldSignature(JavaFieldSignature curField, boolean ext) {
		super(curField.name, curField.modifiers, curField.type,
				curField.viewTags, ext || curField.ext);
	}

	@Override
	public String toString() {
		StringBuilder signature = new StringBuilder(modifiers);
		if (!modifiers.isEmpty()) {
			signature.append(' ');
		}
		signature.append(type);
		signature.append(' ');
		signature.append(name);
		
		return signature.toString();
	}

	@Override
	public int hashCode() {
		StringBuilder signature = new StringBuilder(modifiers);
		signature.append(type);
		signature.append(name);
		
		return signature.toString().hashCode();
	}

	@Override
	public JavaFieldSignature createExtendedSignature() {
		return new JavaFieldSignature(this, true);
	}
}
