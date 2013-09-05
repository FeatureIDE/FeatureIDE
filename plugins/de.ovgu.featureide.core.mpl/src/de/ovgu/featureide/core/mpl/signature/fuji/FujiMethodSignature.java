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
package de.ovgu.featureide.core.mpl.signature.fuji;

import java.util.Arrays;
import java.util.LinkedList;

import AST.Access;
import AST.List;
import AST.ParameterDeclaration;
import AST.TypeDecl;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractMethodSignature;

/**
 * Holds the java signature of a method.
 * 
 * @author Sebastian Krieter
 */
public class FujiMethodSignature extends AbstractMethodSignature {

	protected TypeDecl returnType;
	protected List<ParameterDeclaration> parameterList;
	protected List<Access> exceptionList;
//	protected final boolean isConstructor;

	public FujiMethodSignature(AbstractClassSignature parent, String name, 
			String modifier, TypeDecl returnType, boolean isConstructor,
			List<ParameterDeclaration> parameterList, List<Access> exceptionList) {
//		super(parent, name, modifier, returnType.name());
		super(parent, name, modifier, returnType.name(), new LinkedList<String>(), isConstructor);
		this.returnType = returnType;
		this.parameterList = parameterList;
		this.exceptionList = exceptionList;
//		this.isConstructor = isConstructor;
	}

//	public FujiMethodSignature(FujiMethodSignature orgSig) {
//		this(orgSig, false);
//	}
//
//	private FujiMethodSignature(FujiMethodSignature orgSig, boolean ext) {
//		super(orgSig, ext);
////		isConstructor = orgSig.isConstructor;
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
		for (int i = 0; i < parameterList.getNumChild(); i++) {
			if (i > 0)
				methodString.append(", ");
			methodString.append(parameterList.getChild(i).type().name());
			methodString.append(" arg");
			methodString.append(i);
		}
		methodString.append(')');

		return methodString.toString();
	}

//	@Override
//	public FujiMethodSignature createExtendedSignature() {
//		return new FujiMethodSignature(this, true);
//	}

	@Override
	protected void computeHashCode() {
		hashCode = 1;
		hashCode = hashCodePrime * hashCode + fullName.hashCode();
		hashCode = hashCodePrime * hashCode + Arrays.hashCode(modifiers);
		hashCode = hashCodePrime * hashCode + type.hashCode();
		
		hashCode = hashCodePrime * hashCode + (isConstructor ? 1231 : 1237);
		for (ParameterDeclaration parameter : parameterList) {
			hashCode = hashCodePrime * hashCode + parameter.type().toString().hashCode();
		}
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null || getClass() != obj.getClass())
			return false;
		
		FujiMethodSignature otherSig = (FujiMethodSignature) obj;
		
		if (!super.sigEquals(otherSig)) 
			return false;
		if (isConstructor != otherSig.isConstructor 
				|| !returnType.sameStructure(otherSig.returnType)
				|| parameterList.getNumChild() != otherSig.parameterList.getNumChild()) {
			return false;
		}
		
		for (int i = 0; i < parameterList.getNumChild(); i++) {
			if (!parameterList.getChild(i).type().sameStructure(
					otherSig.parameterList.getChild(i).type())) {
				return false;
			}
		}
		return true;
	}

//	public static FujiMethodSignature superSignature(
//			LinkedList<FujiMethodSignature> sigs) {
//		return null;
//	}
}
