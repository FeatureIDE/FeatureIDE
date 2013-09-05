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

import AST.ImportDecl;
import AST.List;
import AST.TypeDecl;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassSignature;

/**
 * Holds the java signature of a class.
 * 
 * @author Sebastian Krieter
 */
public class FujiClassSignature extends AbstractClassSignature {
	
	protected final TypeDecl typeDecl;
	protected final List<ImportDecl> importList;
	
	public FujiClassSignature(AbstractClassSignature parent, String name, String modifiers, 
			String type, String pckg, TypeDecl typeDecl, List<ImportDecl> importList) {
		super(parent, name, modifiers, type, pckg);
		this.typeDecl = typeDecl;
		this.importList = importList;
	}
	
//	public FujiClassSignature(FujiClassSignature orgSig) {
//		this(orgSig, false);
//	}
//	
//	private FujiClassSignature(FujiClassSignature orgSig, boolean ext) {
//		super(orgSig, ext);
//		this.typeDecl = orgSig.typeDecl;
//		this.importList = orgSig.importList;
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
//	public FujiClassSignature createExtendedSignature() {
//		return new FujiClassSignature(this, true);
//	}

	@Override
	protected void computeHashCode() {
		super.computeHashCode();
		hashCode *= hashCodePrime;
		for (String extend : extendList) {
			hashCode += extend.hashCode();
		}
		hashCode *= hashCodePrime;
		for (String implement : implementList) {
			hashCode += implement.hashCode();
		}
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null || getClass() != obj.getClass())
			return false;
		
		FujiClassSignature otherSig = (FujiClassSignature) obj;
		
		if (!super.sigEquals(otherSig)) 
			return false;
		
		if (!typeDecl.sameStructure(otherSig.typeDecl)) {
			return false;
		}
		
//		if (extendList.size() != otherSig.extendList.size()
//				|| implementList.size() != otherSig.implementList.size()) {
//			return false;
//		}
//		
//		for (String thisExtend : extendList) {
//			if (!otherSig.extendList.contains(thisExtend)) {
//				return false;
//			}
//		}
//		for (String thisImplement : implementList) {
//			if (!otherSig.implementList.contains(thisImplement)) {
//				return false;
//			}
//		}
		return true;
	}
}
