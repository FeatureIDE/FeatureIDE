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
package de.ovgu.featureide.fm.core.base.impl;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelProperty;
import de.ovgu.featureide.fm.core.filter.ConcreteFeatureFilter;
import de.ovgu.featureide.fm.core.filter.base.Filter;

/**
 * The model representation of the feature tree that notifies listeners of
 * changes in the tree.
 * 
 * @author Thomas Thuem
 * @author Florian Proksch
 * @author Stefan Krueger
 * @author Sebastian Krieter
 * 
 */
public class FeatureModelProperty implements IFeatureModelProperty {

	private final IFeatureModel correspondingFeatureModel;

	/**
	 * All comment lines from the model file without line number at which they
	 * occur
	 */
	private final List<String> comments;

	/**
	 * Saves the annotations from the model file as they were read,
	 * because they were not yet used.
	 */
	private final List<String> annotations;

	/**
	 * A list containing the feature names in their specified order will be
	 * initialized in XmlFeatureModelReader.
	 */
	private final List<String> featureOrderList;

	private boolean featureOrderUserDefined;

	private boolean featureOrderInXML;

	public FeatureModelProperty(IFeatureModel correspondingFeatureModel) {
		this.correspondingFeatureModel = correspondingFeatureModel;

		this.featureOrderList = new LinkedList<String>();
		this.featureOrderUserDefined = false;
		this.featureOrderInXML = false;

		this.comments = new LinkedList<String>();
		this.annotations = new LinkedList<String>();
	}

	public FeatureModelProperty(IFeatureModelProperty property, IFeatureModel correspondingFeatureModel) {
		this.correspondingFeatureModel = correspondingFeatureModel;

		this.featureOrderUserDefined = property.isFeatureOrderUserDefined();
		if (this.featureOrderUserDefined) {
			this.featureOrderList = new LinkedList<String>(property.getFeatureOrderList());
		} else {
			this.featureOrderList = new LinkedList<String>();
		}
		this.featureOrderInXML = property.isFeatureOrderInXML();

		this.comments = new LinkedList<>(property.getComments());
		this.annotations = new LinkedList<>(property.getAnnotations());
	}

	@Override
	public void addAnnotation(String annotation) {
		annotations.add(annotation);

	}

	@Override
	public void addComment(String comment) {
		comments.add(comment);
	}

	@Override
	public List<String> getAnnotations() {
		return Collections.unmodifiableList(annotations);
	}

	@Override
	public List<String> getComments() {
		return Collections.unmodifiableList(comments);
	}

	@Override
	public IFeatureModel getFeatureModel() {
		return correspondingFeatureModel;
	}

	@Override
	public List<String> getFeatureOrderList() {
		if (featureOrderList.isEmpty()) {
			return Filter.toString(correspondingFeatureModel.getFeatures(), new ConcreteFeatureFilter());
		}
		return featureOrderList;
	}

	@Override
	public boolean isFeatureOrderInXML() {
		return featureOrderInXML;
	}

	@Override
	public boolean isFeatureOrderUserDefined() {
		return featureOrderUserDefined;
	}

	@Override
	public void setFeatureOrderInXML(boolean featureOrderInXML) {
		this.featureOrderInXML = featureOrderInXML;
	}

	@Override
	public void setFeatureOrderList(List<String> featureOrderList) {
		this.featureOrderList.clear();
		this.featureOrderList.addAll(featureOrderList);
	}

	@Override
	public void setFeatureOrderUserDefined(boolean featureOrderUserDefined) {
		this.featureOrderUserDefined = featureOrderUserDefined;
	}

}
