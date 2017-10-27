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

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.base.IFeature;

/**
 * TODO description
 * 
 * @author steffen
 */
public class FeatureSignatureHierarchy {

	private final IFeature feature;

	private final int featureId;

	private final Set<ExtendedPullUpSignature> children;

	public FeatureSignatureHierarchy(final IFeature feature, final int featureId) {
		this.feature = feature;
		this.featureId = featureId;
		this.children = new HashSet<>();
	}

	public IFeature getFeature() {
		return feature;
	}

	public int getFeatureId() {
		return featureId;
	}

	public Set<ExtendedPullUpSignature> getChildren() {
		return children;
	}

	public void addChild(ExtendedPullUpSignature extendSignature) {
		this.children.add(extendSignature);
	}

}
