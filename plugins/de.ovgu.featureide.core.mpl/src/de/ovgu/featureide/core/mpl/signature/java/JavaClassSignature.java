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

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map.Entry;

import de.ovgu.featureide.core.mpl.signature.AbstractClassSignature;
import de.ovgu.featureide.core.mpl.signature.ViewTag;

/**
 * Holds the java signature of a class.
 * 
 * @author Sebastian Krieter
 */
public class JavaClassSignature extends AbstractClassSignature<JavaClassSignature> {
	
	public JavaClassSignature(String name, String modifiers, String type, String pckg, LinkedList<ViewTag> viewTags, boolean ext) {
		super(name, modifiers, type, pckg, viewTags, ext);
		
		fields = new HashSet<JavaFieldSignature>();
		methods = new HashSet<JavaMethodSignature>();
		innerClasses = new HashMap<String, JavaClassSignature>();
		importList = new HashSet<String>();
		extendList = new HashSet<String>();
		implementList = new HashSet<String>();
	}
	
	public JavaClassSignature(String name, String modifiers, String type, String pckg, boolean ext) {
		this(name, modifiers, type, pckg, null, ext);
	}

	@Override
	public int hashCode() {
		StringBuilder sb = new StringBuilder();
		if (!pckg.isEmpty()) {
			sb.append(pckg);
		}

		for (String ext : extendList) {
			sb.append(ext);
		}		
		for (String impl : implementList) {
			sb.append(impl);
		}
		
		int hc = sb.toString().hashCode();
		
		for (JavaFieldSignature field : fields) {
			hc += field.hashCode();
		}
		for (JavaMethodSignature method : methods) {
			hc += method.hashCode();
		}
		for (JavaClassSignature innerClass : getInnerClasses().values()) {
			hc += innerClass.hashCode();
		}
		
		return hc;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (!super.equals(obj)) {
			return false;
		}
		
		JavaClassSignature otherSig = (JavaClassSignature) obj;
		
		if (!pckg.equals(otherSig.pckg)) {
			return false;
		}
		if (extendList.size() != otherSig.extendList.size()) {
			return false;
		}
		if (implementList.size() != otherSig.implementList.size()) {
			return false;
		}
		if (fields.size() != otherSig.fields.size()) {
			return false;
		}
		if (methods.size() != otherSig.methods.size()) {
			return false;
		}
		if (getInnerClasses().size() != otherSig.getInnerClasses().size()) {
			return false;
		}
		
		for (String ext : extendList) {
			if (!otherSig.extendList.contains(ext)) {
				return false;
			}
		}
		for (String impl : implementList) {
			if (!otherSig.implementList.contains(impl)) {
				return false;
			}
		}
		for (JavaFieldSignature field : fields) {
			if (!otherSig.fields.contains(field)) {
				return false;
			}
		}
		for (JavaMethodSignature method : methods) {
			if (!otherSig.methods.contains(method)) {
				return false;
			}
		}
		for (Entry<String, JavaClassSignature> innerClassEntrySet : getInnerClasses().entrySet()) {
			JavaClassSignature otherInnerClassSig = otherSig.getInnerClasses().get(innerClassEntrySet.getKey());
			if (otherInnerClassSig == null || !otherInnerClassSig.equals(innerClassEntrySet.getValue())) {
				return false;
			}
		}
		
		return true;
	}
}
