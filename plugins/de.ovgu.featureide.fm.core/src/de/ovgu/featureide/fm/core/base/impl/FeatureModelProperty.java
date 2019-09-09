/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Objects;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelProperty;

/**
 * All additional properties of one {@link IFeature} instance.
 *
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 */
public class FeatureModelProperty extends MapPropertyContainer implements IFeatureModelProperty {

	@Override
	public int hashCode() {
		return super.hashCode() * Objects.hash(featureOrderInXML, annotations, comments);
	}

	@Override
	public boolean equals(Object obj) {
		if (super.equals(obj)) {
			final FeatureModelProperty other = (FeatureModelProperty) obj;
			return (featureOrderInXML == other.featureOrderInXML) && Objects.equals(annotations, other.annotations) && Objects.equals(comments, other.comments);
		} else {
			return false;
		}
	}

	/**
	 * Saves the annotations from the model file as they were read, because they were not yet used.
	 */
	protected final List<String> annotations;

	/**
	 * All comment lines from the model file without line number at which they occur
	 */
	protected final List<String> comments;

	protected final IFeatureModel correspondingFeatureModel;

	protected boolean featureOrderInXML;

	protected FeatureModelProperty(FeatureModelProperty oldProperty, IFeatureModel correspondingFeatureModel) {
		super(oldProperty);
		this.correspondingFeatureModel = correspondingFeatureModel != null ? correspondingFeatureModel : oldProperty.correspondingFeatureModel;

		featureOrderInXML = oldProperty.featureOrderInXML;

		comments = new LinkedList<>(oldProperty.comments);
		annotations = new LinkedList<>(oldProperty.annotations);
	}

	public FeatureModelProperty(IFeatureModel correspondingFeatureModel) {
		super();
		this.correspondingFeatureModel = correspondingFeatureModel;

		featureOrderInXML = false;

		comments = new LinkedList<>();
		annotations = new LinkedList<>();
	}

	@Override
	public void addAnnotation(CharSequence annotation) {
		annotations.add(annotation.toString());

	}

	@Override
	public void addComment(CharSequence comment) {
		comments.add(comment.toString());
	}

	@Override
	public IFeatureModelProperty clone(IFeatureModel newFeatureNodel) {
		return new FeatureModelProperty(this, newFeatureNodel);
	}

	@Override
	public Collection<String> getAnnotations() {
		return annotations;
	}

	@Override
	public Collection<String> getComments() {
		return comments;
	}

	@Override
	public IFeatureModel getFeatureModel() {
		return correspondingFeatureModel;
	}

	@Override
	public boolean isFeatureOrderInXML() {
		return featureOrderInXML;
	}

	@Override
	public void reset() {
		featureOrderInXML = false;
		comments.clear();
		annotations.clear();
		properties.clear();
	}

	@Override
	public void setFeatureOrderInXML(boolean featureOrderInXML) {
		this.featureOrderInXML = featureOrderInXML;
	}

}
