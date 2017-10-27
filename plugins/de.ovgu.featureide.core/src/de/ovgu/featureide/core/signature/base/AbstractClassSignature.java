/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.core.signature.base;

import java.util.HashSet;
import java.util.Set;

/**
 * Abstract signature for one class.
 *
 * @author Sebastian Krieter
 */
public abstract class AbstractClassSignature extends AbstractSignature {

	public static final String TYPE_INTERFACE = "interface";
	public static final String TYPE_CLASS = "class";

	protected final String pckg;

	protected final HashSet<String> importList, extendList, implementList, subClassesList;

	protected final Set<AbstractMethodSignature> methods;
	protected final Set<AbstractFieldSignature> fields;
	protected final Set<AbstractClassSignature> memberClasses;

	protected AbstractClassSignature(AbstractClassSignature parent, String name, String modifiers, String type, String pckg) {
		super(parent, name, modifiers, type);
		this.pckg = pckg == null ? "" : pckg;
		if (parent == null) {
			setFullName(this.pckg);
		}
		importList = new HashSet<String>();
		extendList = new HashSet<String>();
		implementList = new HashSet<String>();
		subClassesList = new HashSet<String>();
		methods = new HashSet<>();
		fields = new HashSet<>();
		memberClasses = new HashSet<>();
	}

	public String getPackage() {
		return pckg;
	}

	public HashSet<String> getImportList() {
		return importList;
	}

	public HashSet<String> getExtendList() {
		return extendList;
	}

	public HashSet<String> getImplementList() {
		return implementList;
	}

	public HashSet<String> getSubClassesList() {
		return subClassesList;
	}

	public void addImport(String imp) {
		importList.add(imp);
	}

	public void addImplement(String implement) {
		implementList.add(implement);
		hasHashCode = false;
	}

	public void addExtend(String extend) {
		extendList.add(extend);
		hasHashCode = false;
	}

	public void addSubClass(String subClass) {
		subClassesList.add(subClass);
		hasHashCode = false;
	}

	public void addMethod(AbstractMethodSignature method) {
		methods.add(method);
		hasHashCode = false;
	}

	public Set<AbstractMethodSignature> getMethods() {
		return methods;
	}

	public void addField(AbstractFieldSignature field) {
		fields.add(field);
		hasHashCode = false;
	}

	public Set<AbstractFieldSignature> getFields() {
		return fields;
	}

	public void addMemberClass(AbstractClassSignature memberClass) {
		memberClasses.add(memberClass);
		hasHashCode = false;
	}

	public Set<AbstractClassSignature> getMemberClasses() {
		return memberClasses;
	}

	public boolean isInterface() {
		return this.type.equals(TYPE_INTERFACE);
	}

//	@Override
//	protected void computeHashCode() {
//		hashCode = 1;
//		hashCode = hashCodePrime * hashCode + fullName.hashCode();
//		hashCode = hashCodePrime * hashCode + Arrays.hashCode(modifiers);
//		hashCode = hashCodePrime * hashCode + type.hashCode();
//
//		hashCode *= hashCodePrime;
//		for (String extend : extendList) {
//			hashCode += extend.hashCode();
//		}
//		hashCode *= hashCodePrime;
//		for (String implement : implementList) {
//			hashCode += implement.hashCode();
//		}
//	}

//	@Override
//	public boolean equals(Object obj) {
//		if (this == obj)
//			return true;
//		if (obj == null || getClass() != obj.getClass())
//			return false;
//
//		AbstractClassSignature otherSig = (AbstractClassSignature) obj;
//
//		if (!super.sigEquals(otherSig))
//			return false;
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
//		return true;
//	}
}
