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
package de.ovgu.featureide.fm.attributes.base.impl;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.fm.attributes.base.IExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.MultiFeature;

/**
 * This class extends {@link MultiFeature} to support usage of attributes for features in {@link ExtendedMultiFeatureModel}s. Instances of this class can be
 * created by {@link ExtendedMultiFeatureModelFactory}.
 * 
 * @author Rahel Arens
 * @author Johannes Herschel
 */
public class ExtendedMultiFeature extends MultiFeature implements IExtendedFeature {

	protected List<IFeatureAttribute> attributes;

	public ExtendedMultiFeature(IFeatureModel featureModel, String name) {
		super(featureModel, name);

		// Create empty attributes list
		attributes = Collections.synchronizedList(new LinkedList<IFeatureAttribute>());
	}

	protected ExtendedMultiFeature(ExtendedMultiFeature copyFeature, IFeatureModel featureModel, IFeatureStructure featureStructure) {
		super(copyFeature, featureModel, featureStructure);

		// Copy all attributes from the copy feature
		attributes = Collections.synchronizedList(new LinkedList<IFeatureAttribute>());
		for (IFeatureAttribute attribute : copyFeature.getAttributes()) {
			attributes.add(attribute.cloneAtt(this));
		}
	}

	@Override
	public List<IFeatureAttribute> getAttributes() {
		return attributes;
	}

	@Override
	public void addAttribute(IFeatureAttribute attribute) {
		attributes.add(attribute);
	}

	@Override
	public void removeAttribute(IFeatureAttribute attribute) {
		attributes.remove(attribute);
	}

	@Override
	public boolean isContainingAttribute(IFeatureAttribute attribute) {
		return attributes.stream().anyMatch(a -> attribute.getName().equals(a.getName()));
	}

	@Override
	public ExtendedMultiFeature clone(IFeatureModel newFeatureModel, IFeatureStructure newStructure) {
		return new ExtendedMultiFeature(this, newFeatureModel, newStructure);
	}

	@Override
	public String createTooltip(Object... objects) {
		StringBuilder tooltip = new StringBuilder(super.createTooltip(objects));
		return ExtendedFeature.createExtendedTooltip(attributes, tooltip);
	}
}
