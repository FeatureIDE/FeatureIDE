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

import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;

/**
 * Contains all information needed to execute commands that move features.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 * @author Benedikt Jutz
 */
public class FeatureOperationData {

	/**
	 * <code>feature</code> is the graphical feature we just moved.
	 */
	public final IGraphicalFeature feature;
	/**
	 * <code>oldParent</code> is the parent feature that <code>feature</code> had before movement.
	 */
	public final IGraphicalFeature oldParent;
	/**
	 * <code>oldIndex</code> is the position <code>feature</code> had for <code>oldFeature</code>.
	 */
	public final int oldIndex;
	/**
	 * <code>newParent</code> is the parent feature <code>feature</code> will have after movement.
	 */
	public final IGraphicalFeature newParent;
	/**
	 * <code>newIndex</code> is the position <code>feature</code> will have for <code>newParent</code>.
	 */
	public final int newIndex;
	/**
	 * <code>or</code> encodes if <code>oldParent</code> had an or-group before movement.
	 */
	public final boolean or;
	/**
	 * <code>alternative</code> encodes if <code>oldParent</code> had an alternative-group before movement.
	 */
	public final boolean alternative;
	/**
	 * <code>reverse</code> encodes if this movement operation is a reversal of another operation.
	 */
	public final boolean reverse;

	/**
	 * Creates new {@link FeatureOperationData}.
	 *
	 * @param feature - {@link IGraphicalFeature}
	 * @param oldParent - {@link IGraphicalFeature}
	 * @param newParent - {@link IGraphicalFeature}
	 * @param newIndex - int
	 * @param oldIndex - int
	 * @param or - boolean
	 * @param alternative - boolean
	 * @param reverse - boolean
	 */
	public FeatureOperationData(IGraphicalFeature feature, IGraphicalFeature oldParent, IGraphicalFeature newParent, int oldIndex, int newIndex, boolean or,
			boolean alternative, boolean reverse) {
		this.feature = feature;
		this.newIndex = newIndex;
		this.newParent = newParent;
		this.oldIndex = oldIndex;
		this.oldParent = oldParent;
		this.or = or;
		this.alternative = alternative;
		this.reverse = reverse;
	}

	/**
	 * Swaps <code>oldFeature</code> with <code>newFeature</code> and <code>oldIndex</code> with <code>newIndex</code> in order to undo the feature movement.
	 *
	 * @return new {@link FeatureOperationData}
	 */
	public FeatureOperationData getInverseData() {
		return new FeatureOperationData(feature, newParent, oldParent, newIndex, oldIndex, or, alternative, true);
	}
}
