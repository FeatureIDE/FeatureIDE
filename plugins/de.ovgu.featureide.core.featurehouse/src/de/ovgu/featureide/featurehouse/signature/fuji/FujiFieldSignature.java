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
package de.ovgu.featureide.featurehouse.signature.fuji;

import AST.TypeDecl;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractFieldSignature;

/**
 * Holds the java signature of a field.
 *
 * @author Sebastian Krieter
 */
public class FujiFieldSignature extends AbstractFieldSignature {

	protected TypeDecl returnType;

	public FujiFieldSignature(AbstractClassSignature parent, String name, String modifiers, TypeDecl returnType) {
		super(parent, name, modifiers, returnType.name());
		this.returnType = returnType;
	}

	@Override
	public String toString() {
		final StringBuilder fieldString = new StringBuilder();

//		fieldString.append(super.toString());
//		if (fieldString.length() > 0) {
//			fieldString.append(LINE_SEPARATOR);
//		}

		if (mergedjavaDocComment != null) {
			fieldString.append(mergedjavaDocComment);
		}

		if (modifiers.length > 0) {
			for (final String modifier : modifiers) {
				fieldString.append(modifier);
				fieldString.append(' ');
			}
		}
		fieldString.append(type);
		fieldString.append(' ');
		fieldString.append(name);

		return fieldString.toString();
	}

	@Override
	protected void computeHashCode() {
		super.computeHashCode();
		hashCode = (hashCodePrime * hashCode) + type.hashCode();
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if ((obj == null) || (getClass() != obj.getClass())) {
			return false;
		}

		final FujiFieldSignature otherSig = (FujiFieldSignature) obj;

		if (!super.sigEquals(otherSig) || (returnType != otherSig.returnType)) {
			return false;
		}
		return true;
	}
}
