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
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import static de.ovgu.featureide.fm.core.localization.StringTable.MOVE_FEATURE;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.PropertyConstants;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Operation with functionality to move features. Provides redo/undo support.
 * 
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class FeatureMoveOperation extends AbstractFeatureModelOperation {

	private FeatureOperationData data;
	private Point newPos;
	private Point oldPos;
	private IFeature feature;

	public FeatureMoveOperation(FeatureOperationData data, Object editor, Point newPos, Point oldPos, IFeature feature) {
		super(feature.getFeatureModel(), MOVE_FEATURE);
		this.data = data;
		this.newPos = newPos;
		this.oldPos = oldPos;
		this.feature = feature;
		setEditor(editor);
		setEventId(PropertyConstants.STRUCTURE_CHANGED);
	}

//	public void newInnerOrder(Point newPos) {
//		FeatureUIHelper.setLocation(feature, newPos);
//		if (!data.getFeature().getTree().isRoot()) {
//			data.getOldParent().getStructure().removeChild(data.getFeature().getStructure());
//			LinkedList<IFeature> featureList = new LinkedList<IFeature>(FeatureUtils.convertToFeatureList(data.getOldParent().getStructure().getChildren()));
//			LinkedList<IFeature> newFeatureList = new LinkedList<IFeature>();
//			int counter2 = 0;
//			int counter = 0;
//
//			while (data.getOldParent().getStructure().hasChildren()) {
//				if (counter == counter2) {
//					if (FeatureUIHelper.hasVerticalLayout(featureModel)) {
//						if (FeatureUIHelper.getLocation(featureList.get(counter)).y > newPos.y) {
//							newFeatureList.add(data.getFeature());
//							counter = Integer.MIN_VALUE;
//						}
//					} else {
//						if (FeatureUIHelper.getLocation(featureList.get(counter)).x > newPos.x) {
//							newFeatureList.add(data.getFeature());
//							counter = Integer.MIN_VALUE;
//						}
//					}
//				}
//
//				data.getOldParent().getStructure().removeChild(featureList.get(counter2).getStructure());
//				newFeatureList.add(featureList.get(counter2));
//				counter2++;
//				counter++;
//			}
//
//			if (!newFeatureList.contains(data.getFeature())) {
//				newFeatureList.add(data.getFeature());
//			}
//
//			for (int i = 0; i < counter2 + 1; i++) {
//				data.getOldParent().getStructure().addChildAtPosition(i, newFeatureList.get(i).getStructure());
//			}
//		}
//
//	}

	@Override
	protected void redo() {
//		if (!featureModel.getGraphicRepresenation().getLayout().hasFeaturesAutoLayout()) {
//			newInnerOrder(newPos);
//		} else {
			try {
				data.getOldParent().getObject().getStructure().removeChild(data.getFeature().getObject().getStructure());
				data.getNewParent().getObject().getStructure().addChildAtPosition(data.getNewIndex(), data.getFeature().getObject().getStructure());
			} catch (Exception e) {
				FMUIPlugin.getDefault().logError(e);
			}
//		}
	}

	@Override
	protected void undo() {
//		if (!featureModel.getGraphicRepresenation().getLayout().hasFeaturesAutoLayout()) {
//			newInnerOrder(oldPos);
//		} else {
			try {
				final IFeatureStructure structure2 = data.getFeature().getObject().getStructure();
				data.getNewParent().getObject().getStructure().removeChild(structure2);
				if (data.getOldParent() != null) {
					final IFeatureStructure structure = data.getOldParent().getObject().getStructure();
					structure.addChildAtPosition(data.getOldIndex(), structure2);
				}
			} catch (Exception e) {
				FMUIPlugin.getDefault().logError(e);
			}
//		}
	}

}
