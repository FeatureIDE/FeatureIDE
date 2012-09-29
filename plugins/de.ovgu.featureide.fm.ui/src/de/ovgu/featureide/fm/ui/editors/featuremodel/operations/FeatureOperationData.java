/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import de.ovgu.featureide.fm.core.Feature;

/**
 * contains all information needed to execute commands that move features * @author
 * 
 * @author Fabian Benduhn
 */
public class FeatureOperationData {

	private Feature oldParent;
	private Feature feature;
	private Feature newParent;
	private int newIndex;
	private int oldIndex;

	public FeatureOperationData(Feature feature, Feature oldParent,
			Feature newParent, int newIndex, int oldIndex) {
		this.feature = feature;
		this.newIndex = newIndex;
		this.newParent = newParent;
		this.oldIndex = oldIndex;
		this.oldParent = oldParent;

	}

	/**
	 * @return the oldParent
	 */
	public Feature getOldParent() {
		return oldParent;
	}

	/**
	 * @param oldParent
	 *            the oldParent to set
	 */
	public void setOldParent(Feature oldParent) {
		this.oldParent = oldParent;
	}

	/**
	 * @return the feature
	 */
	public Feature getFeature() {
		return feature;
	}

	/**
	 * @param feature
	 *            the feature to set
	 */
	public void setFeature(Feature feature) {
		this.feature = feature;
	}

	/**
	 * @return the newParent
	 */
	public Feature getNewParent() {
		return newParent;
	}

	/**
	 * @param newParent
	 *            the newParent to set
	 */
	public void setNewParent(Feature newParent) {
		this.newParent = newParent;
	}

	/**
	 * @return the newIndex
	 */
	public int getNewIndex() {
		return newIndex;
	}

	/**
	 * @param newIndex
	 *            the newIndex to set
	 */
	public void setNewIndex(int newIndex) {
		this.newIndex = newIndex;
	}

	/**
	 * @return the oldIndex
	 */
	public int getOldIndex() {
		return oldIndex;
	}

	/**
	 * @param oldIndex
	 *            the oldIndex to set
	 */
	public void setOldIndex(int oldIndex) {
		this.oldIndex = oldIndex;
	}

}