/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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

import static de.ovgu.featureide.fm.core.localization.StringTable.COLLAPSE_SIBLINGS;

import java.util.LinkedList;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * TODO description
 * 
 * @author Max
 */
public class SetFeaturesToCollapsedOperation extends AbstractFeatureModelOperation {

	private IFeature feature;

	private LinkedList<IFeatureStructure> affectedFeatureList = new LinkedList<IFeatureStructure>();

	/**
	 * @param label
	 *            Description of this operation to be used in the menu
	 * @param feature
	 *            feature on which this operation will be executed
	 * 
	 */
	public SetFeaturesToCollapsedOperation(IFeature feature, IFeatureModel featureModel) {
		super(featureModel, getLabel(feature));
		this.feature = feature;
	}

	/**
	 * @param feature
	 * @return String to be used in undo/redo menu
	 */
	private static String getLabel(IFeature feature) {
		return COLLAPSE_SIBLINGS;
	}

	@Override
	protected FeatureIDEEvent operation() {
		for (IFeatureStructure f : feature.getStructure().getParent().getChildren()) {
			affectedFeatureList.add(f);
			if (!f.equals(feature.getStructure())) {
				f.setCollapsed(true);
			}
		}
		return new FeatureIDEEvent(feature, EventType.COLLAPSED_CHANGED);
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		for (IFeatureStructure f : affectedFeatureList) {
			f.setCollapsed(f.isCollapsed());
		}
		return new FeatureIDEEvent(feature, EventType.COLLAPSED_CHANGED);
		//		return operation();
	}

}
