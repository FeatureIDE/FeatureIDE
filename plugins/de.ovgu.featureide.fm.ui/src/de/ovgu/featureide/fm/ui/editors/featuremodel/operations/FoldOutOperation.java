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

import static de.ovgu.featureide.fm.core.localization.StringTable.FOLD_OUT_FEATURE;

import java.util.List;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Operation with functionality to expand a Feature. Enables undo/redo functionality.
 * 
 * @author Joshua Sprey
 * @author Enis Belli
 */
public class FoldOutOperation extends AbstractFeatureModelOperation {
	IFeature selectedFeature;
	List<IFeatureStructure> child;

	public FoldOutOperation(IFeatureModel featureModel, IFeature selectedFeature) {
		super(featureModel, FOLD_OUT_FEATURE);
		// TODO Auto-generated constructor stub
		this.selectedFeature = selectedFeature;
		child = selectedFeature.getStructure().getChildren();
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AbstractFeatureModelOperation#operation()
	 */
	@Override
	protected FeatureIDEEvent operation() {
		// TODO Auto-generated method stub
		FMUIPlugin.getDefault().logInfo("Before Fold out call");
//		for (IFeatureStructure iFeatureStructure : child) {
//			iFeatureStructure.setCollapsed(false);
//		}
		selectedFeature.getStructure().setCollapsed(false);
		return new FeatureIDEEvent(featureModel, EventType.FOLD_OUT_FEATURE);
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AbstractFeatureModelOperation#inverseOperation()
	 */
	@Override
	protected FeatureIDEEvent inverseOperation() {
		// TODO Auto-generated method stub
//		for (IFeatureStructure iFeatureStructure : child) {
//			iFeatureStructure.setCollapsed(true);
//		}
		selectedFeature.getStructure().setCollapsed(true);
		return new FeatureIDEEvent(featureModel, EventType.FOLD_OUT_FEATURE);
	}

}
