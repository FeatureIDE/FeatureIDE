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
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

/**
 * Contains all information needed to execute commands that move features
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class FeatureOperationData {

	private String oldParentName;
	private String featureName;
	private String newParentName;
	private int newIndex;
	private int oldIndex;

	public FeatureOperationData(String featureName, String oldParentName, String newParentName, int newIndex, int oldIndex) {
		this.featureName = featureName;
		this.newIndex = newIndex;
		this.newParentName = newParentName;
		this.oldIndex = oldIndex;
		this.oldParentName = oldParentName;
	}

	/**
	 * @return the oldParentName
	 */
	public String getOldParentName() {
		return oldParentName;
	}

	/**
	 * @param oldParentName the oldParentName to set
	 */
	public void setOldParentName(String oldParentName) {
		this.oldParentName = oldParentName;
	}

	/**
	 * @return the featureName
	 */
	public String getFeatureName() {
		return featureName;
	}

	/**
	 * @param featureName the featureName to set
	 */
	public void setFeatureName(String featureName) {
		this.featureName = featureName;
	}

	/**
	 * @return the newParentName
	 */
	public String getNewParentName() {
		return newParentName;
	}

	/**
	 * @param newParentName the newParentName to set
	 */
	public void setNewParentName(String newParentName) {
		this.newParentName = newParentName;
	}

	/**
	 * @return the newIndex
	 */
	public int getNewIndex() {
		return newIndex;
	}

	/**
	 * @param newIndex the newIndex to set
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
	 * @param oldIndex the oldIndex to set
	 */
	public void setOldIndex(int oldIndex) {
		this.oldIndex = oldIndex;
	}

}
