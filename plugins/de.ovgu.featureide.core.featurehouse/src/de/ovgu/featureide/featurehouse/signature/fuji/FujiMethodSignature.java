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

import java.util.Iterator;
import java.util.LinkedList;

import AST.Access;
import AST.List;
import AST.ParameterDeclaration;
import AST.TypeDecl;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;

/**
 * Holds the java signature of a method.
 *
 * @author Sebastian Krieter
 */
public class FujiMethodSignature extends AbstractMethodSignature {

	protected TypeDecl returnType;
	protected List<ParameterDeclaration> parameterList;
	protected List<Access> exceptionList;

	public FujiMethodSignature(AbstractClassSignature parent, String name, String modifier, TypeDecl returnType, boolean isConstructor,
			List<ParameterDeclaration> parameterList, List<Access> exceptionList) {
		super(parent, name, modifier, returnType.name(), new LinkedList<String>(), isConstructor);
		this.returnType = returnType;
		this.parameterList = parameterList;
		this.exceptionList = exceptionList;
		for (final ParameterDeclaration parameter : parameterList) {
			parameterTypes.add(parameter.type().name());
		}
	}

	@Override
	public String toString() {
		final StringBuilder methodString = new StringBuilder();

//		methodString.append(super.toString());
//		if (methodString.length() > 0) {
//			methodString.append(LINE_SEPARATOR);
//		}

		if (mergedjavaDocComment != null) {
			methodString.append(mergedjavaDocComment);
		}

		if (modifiers.length > 0) {
			for (final String modifier : modifiers) {
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
		boolean notfirst = false;
		for (final ParameterDeclaration parameter : parameterList) {
			if (notfirst) {
				methodString.append(", ");
			} else {
				notfirst = true;
			}
			methodString.append(parameter.type().name());
			methodString.append(' ');
			methodString.append(parameter.name());
		}
		methodString.append(')');

		if (exceptionList.getNumChild() > 0) {
			notfirst = false;
			methodString.append(" throws ");
			for (final Access exception : exceptionList) {
				if (notfirst) {
					methodString.append(", ");
				} else {
					notfirst = true;
				}
				methodString.append(exception.type().name());
			}
		}

		return methodString.toString();
	}

	@Override
	protected void computeHashCode() {
		super.computeHashCode();

		hashCode = (hashCodePrime * hashCode) + type.hashCode();

		hashCode = (hashCodePrime * hashCode) + (isConstructor ? 1231 : 1237);
		for (final ParameterDeclaration parameter : parameterList) {
			hashCode = (hashCodePrime * hashCode) + parameter.type().name().hashCode();
		}
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if ((obj == null) || (getClass() != obj.getClass())) {
			return false;
		}

		final FujiMethodSignature otherSig = (FujiMethodSignature) obj;

		if (!super.sigEquals(otherSig)) {
			return false;
		}
		if (isConstructor != otherSig.isConstructor) {
			return false;
		}

		if (returnType != otherSig.returnType) {
			return false;
		}

		if (parameterList.getNumChild() != otherSig.parameterList.getNumChild()) {
			return false;
		}

		final Iterator<ParameterDeclaration> thisIt = parameterList.iterator();
		final Iterator<ParameterDeclaration> otherIt = otherSig.parameterList.iterator();
		while (thisIt.hasNext()) {
			if (thisIt.next().type() != otherIt.next().type()) {
				return false;
			}
		}

		return true;
	}

	@Override
	public String getReturnType() {
		return returnType.name();
	}
}
