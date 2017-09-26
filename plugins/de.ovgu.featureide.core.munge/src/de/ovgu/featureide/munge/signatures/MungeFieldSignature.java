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
package de.ovgu.featureide.munge.signatures;

import java.lang.reflect.Modifier;

import org.eclipse.jdt.core.dom.Type;

import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractFieldSignature;

/**
 * Holds the java signature of a field.
 *
 * @author Sebastian Krieter
 */
public class MungeFieldSignature extends AbstractFieldSignature {

	public MungeFieldSignature(AbstractClassSignature parent, String name, int modifiers, Type returnType) {
		super(parent, name, Modifier.toString(modifiers), returnType.toString());
	}

	public MungeFieldSignature(AbstractClassSignature parent, String name, int modifiers, Type returnType, int line) {
		super(parent, name, Modifier.toString(modifiers), returnType.toString(), line);
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

		final MungeFieldSignature otherSig = (MungeFieldSignature) obj;

		return super.sigEquals(otherSig);
	}
}
