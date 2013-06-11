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
package de.ovgu.featureide.core.mpl.signature.abstr;

import java.util.LinkedList;

/**
 * Abstract signature for one class.
 * 
 * @author Sebastian Krieter
 */
public abstract class AbstractClassSignature extends AbstractSignature {

	protected final String pckg;

	protected final LinkedList<String> 
		importList, extendList, implementList;
	
	protected AbstractClassSignature(AbstractClassSignature parent, String name, String modifiers, String type, String pckg) {
		super(parent, name, modifiers, type, null);
		this.pckg = pckg == null ? "" : pckg;
		if (parent == null) {
			setFullName(pckg);
		}
		importList = new LinkedList<String>();
		extendList = new LinkedList<String>();
		implementList = new LinkedList<String>();
	}
	
	protected AbstractClassSignature(AbstractClassSignature orgSig, boolean ext) {
		super(orgSig, ext);
		pckg =  orgSig.pckg;
		importList = new LinkedList<String>(orgSig.importList);
		extendList = new LinkedList<String>(orgSig.extendList);
		implementList = new LinkedList<String>(orgSig.implementList);
	}

	public String getPackage() {
		return pckg;
	}
	
	public LinkedList<String> getImportList() {
		return importList;
	}

	public LinkedList<String> getExtendList() {
		return extendList;
	}

	public LinkedList<String> getImplementList() {
		return implementList;
	}

	public void addImport(String imp) {
		if (!importList.contains(imp)) {
			importList.add(imp);
		}
	}

	public void addImplement(String implement) {
		implementList.add(implement);
		hasHashCode = false;
	}

	public void addExtend(String extend) {
		extendList.add(extend);
		hasHashCode = false;
	}

	@Override
	protected void computeHashCode() {
		super.computeHashCode();
		for (String extend : extendList) {
			hashCode = hashCodePrime * hashCode + extend.hashCode();
		}
		for (String implement : implementList) {
			hashCode = hashCodePrime * hashCode + implement.hashCode();
		}
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null || getClass() != obj.getClass())
			return false;
		
		AbstractClassSignature otherSig = (AbstractClassSignature) obj;
		
		if (!super.equals(otherSig)) 
			return false;
		if (extendList.size() != otherSig.extendList.size()
				|| implementList.size() != otherSig.implementList.size()) {
			return false;
		}
		
		for (String thisExtend : extendList) {
			if (!otherSig.extendList.contains(thisExtend)) {
				return false;
			}
		}
		for (String thisImplement : implementList) {
			if (!otherSig.implementList.contains(thisImplement)) {
				return false;
			}
		}
		return true;
	}
}
