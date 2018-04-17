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

import AST.ClassDecl;
import AST.ImportDecl;
import AST.InterfaceDecl;
import AST.List;
import AST.TypeDecl;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;

/**
 * Holds the java signature of a class.
 *
 * @author Sebastian Krieter
 */
public class FujiClassSignature extends AbstractClassSignature {

	protected final List<ImportDecl> importList;

	protected final LinkedList<TypeDecl> superTypes;
	protected final LinkedList<TypeDecl> implementTypes;

	public FujiClassSignature(AbstractClassSignature parent, String name, String modifiers, String type, String pckg, TypeDecl typeDecl,
			List<ImportDecl> importList) {
		super(parent, name, modifiers, type, pckg);
		this.importList = importList;

		superTypes = new LinkedList<TypeDecl>();
		implementTypes = new LinkedList<TypeDecl>();
		if (typeDecl instanceof ClassDecl) {
			final ClassDecl classDecl = (ClassDecl) typeDecl;
			superTypes.add(classDecl.superclass());
			addExtend(classDecl.superclass().name());
			if (!classDecl.name().equals("Object")) {
				addExtend(classDecl.superclass().name());
			}
			final Iterator<TypeDecl> implementInterfaceIt = classDecl.interfacesIterator();
			while (implementInterfaceIt.hasNext()) {
				final TypeDecl implementType = implementInterfaceIt.next();
				implementTypes.add(implementType);
				addImplement(implementType.name());
			}
		} else if (typeDecl instanceof InterfaceDecl) {
			final Iterator<TypeDecl> superInterfaceIt = ((InterfaceDecl) typeDecl).superinterfacesIterator();
			while (superInterfaceIt.hasNext()) {
				final TypeDecl superInterface = superInterfaceIt.next();
				superTypes.add(superInterface);
				if (!superInterface.name().equals("Object")) {
					addExtend(superInterface.name());
				}
			}
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();

//		for (ImportDecl importDecl : importList) {
//			sb.append("import ");
//			sb.append(importDecl.typeName());
//			sb.append(';');
//			sb.append(LINE_SEPARATOR);
//		}

//		sb.append(super.toString());
//		sb.append(LINE_SEPARATOR);

		if (mergedjavaDocComment != null) {
			sb.append(mergedjavaDocComment);
		}

		if (modifiers.length > 0) {
			for (final String modifier : modifiers) {
				sb.append(modifier);
				sb.append(' ');
			}
		}
		sb.append(type);
		sb.append(' ');
		sb.append(name);

		return sb.toString();
	}

	@Override
	protected void computeHashCode() {
		super.computeHashCode();
//		hashCode *= hashCodePrime;
//		for (TypeDecl thisSuperType : superTypes) {
//			hashCode += thisSuperType.hashCode();
//		}
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if ((obj == null) || (getClass() != obj.getClass())) {
			return false;
		}

		final FujiClassSignature otherSig = (FujiClassSignature) obj;

		if (!super.sigEquals(otherSig)) {
			return false;
		}

		if (superTypes.size() != otherSig.superTypes.size()) {
			return false;
		}

		for (final TypeDecl thisSuperType : superTypes) {
			boolean contains = false;
			for (final TypeDecl otherSuperType : otherSig.superTypes) {
				if (thisSuperType == otherSuperType) {
					contains = true;
					break;
				}
			}
			if (!contains) {
				return false;
			}
		}

		return true;
	}
}
