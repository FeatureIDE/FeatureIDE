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
package de.ovgu.featureide.featurehouse.refactoring.pullUp;

import java.util.HashSet;
import java.util.Set;

import de.ovgu.featureide.core.signature.base.AbstractSignature;

/**
 * TODO description
 * 
 * @author steffen
 */
public class ExtendedSignature {

	private final AbstractSignature signature;
	
	private final int featureId;
	
	private final Set<ExtendedSignature> children;
	
	private ExtendedSignature parent;
	
	public ExtendedSignature(final AbstractSignature signature, final int featureId) {
		this.signature = signature;
		this.featureId = featureId;
		this.children = new HashSet<>();
	}

	public Set<ExtendedSignature> getChildren() {
		return children;
	}

	public void addChild(ExtendedSignature child) {
		this.children.add(child);
	}

	public ExtendedSignature getParent() {
		return parent;
	}

	public void setParent(ExtendedSignature parent) {
		this.parent = parent;
	}

	public AbstractSignature getSignature() {
		return signature;
	}

	public int getFeatureId() {
		return featureId;
	}
	
}
