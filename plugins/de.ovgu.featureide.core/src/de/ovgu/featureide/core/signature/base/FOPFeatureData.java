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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * TODO description
 * 
 * @author Sebastian Krieter
 */
public class FOPFeatureData extends AFeatureData {

	private boolean usesExternalMethods, usesOriginal;
	
	private ArrayList<AbstractSignature> calledSignatures;
	private ArrayList<String> usedNonPrimitveTypes;
	
	FOPFeatureData(int id, int startLineNumber, int endLineNumber) {
		super(id, startLineNumber, endLineNumber);
		this.calledSignatures = null;
		this.usesExternalMethods = false;
		this.usesOriginal = false;
	}
	
	public boolean usesExternMethods() {
		return usesExternalMethods;
	}
	
	public boolean usesOriginal() {
		return usesOriginal;
	}

	public List<String> getUsedNonPrimitveTypes() {
		return usedNonPrimitveTypes != null ? Collections.unmodifiableList(usedNonPrimitveTypes) : Collections.<String>emptyList();
	}
	
	public void setUsesExternMethods(boolean usesExternMethods) {
		this.usesExternalMethods = usesExternMethods;
	}
	
	public void setUsesOriginal(boolean usesOriginal) {
		this.usesOriginal = usesOriginal;
	}
	
	public List<AbstractSignature> getCalledSignatures() {
		return calledSignatures != null ? Collections.unmodifiableList(calledSignatures) : Collections.<AbstractSignature>emptyList();
	}
	
	public void addCalledSignature(AbstractSignature signature) {
		if (this.calledSignatures == null) {
			this.calledSignatures = new ArrayList<AbstractSignature>();
		}
		this.calledSignatures.add(signature);
	}
	
	public void addUsedNonPrimitveType(String usedNonPrimitveType) {
		if (this.usedNonPrimitveTypes == null) {
			this.usedNonPrimitveTypes = new ArrayList<String>();
		}
		if (!this.usedNonPrimitveTypes.contains(usedNonPrimitveType)) {
			this.usedNonPrimitveTypes.add(usedNonPrimitveType);
		}
	}
}
