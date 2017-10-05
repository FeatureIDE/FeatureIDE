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
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE_ERROR;
import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE;
import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE_INCLUDING_SUBFEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.UNABLE_TO_DELETE_THIS_FEATURES_UNTIL_ALL_RELEVANT_CONSTRAINTS_ARE_REMOVED_;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * Allows to delete a feature including its sub features
 *
 * @author Jan Wedding
 * @author Melanie Pflaume
 * @author Marcus Pinnecke
 * @author Paul Westphal
 * @author Chico Sundermann
 */
public class FeatureTreeDeleteOperation extends MultiFeatureModelOperation implements GUIDefaults {

	private final IFeature[] featureArray;
	private LinkedList<IFeature> featureList;
	private LinkedList<IFeature> containedFeatureList;

	private LinkedList<IFeature> andList;
	private LinkedList<IFeature> orList;
	private LinkedList<IFeature> alternativeList;

	public FeatureTreeDeleteOperation(IFeatureModel featureModel, IFeature[] parents) {
		super(featureModel, DELETE);
		featureArray = parents;
	}

	@Override
	protected void createSingleOperations() {
		for (IFeature feature : featureArray) {
			featureList = new LinkedList<IFeature>();
			containedFeatureList = new LinkedList<IFeature>();
			andList = new LinkedList<IFeature>();
			alternativeList = new LinkedList<IFeature>();
			orList = new LinkedList<IFeature>();
			final LinkedList<IFeature> list = new LinkedList<IFeature>();
			list.add(feature);
			getFeaturesToDelete(list);
	
			if (containedFeatureList.isEmpty()) {
				for (final IFeature feat : featureList) {
					if (feat.getStructure().isAnd()) {
						andList.add(feat);
					} else if (feat.getStructure().isOr()) {
						orList.add(feat);
					} else if (feat.getStructure().isAlternative()) {
						alternativeList.add(feat);
					}
					final AbstractFeatureModelOperation op = new DeleteFeatureOperation(featureModel, feat);
					operations.add(op);
				}
			} else {
				final String containedFeatures = containedFeatureList.toString();
				final MessageDialog dialog = new MessageDialog(new Shell(), DELETE_ERROR, FEATURE_SYMBOL,
						"The following features are contained in constraints:" + '\n' + containedFeatures.substring(1, containedFeatures.length() - 1) + '\n' + '\n'
							+ UNABLE_TO_DELETE_THIS_FEATURES_UNTIL_ALL_RELEVANT_CONSTRAINTS_ARE_REMOVED_,
						MessageDialog.ERROR, new String[] { IDialogConstants.OK_LABEL }, 0);
	
				dialog.open();
			}
		}
	}

	/**
	 * traverses through the whole subtree and collects the features that should be deleted
	 *
	 * @param linkedList
	 */
	private void getFeaturesToDelete(List<IFeature> linkedList) {
		for (final IFeature feat : linkedList) {
			if (!feat.getStructure().getRelevantConstraints().isEmpty()) {
				containedFeatureList.add(feat);
			}
			if (feat.getStructure().hasChildren()) {
				getFeaturesToDelete(FeatureUtils.convertToFeatureList(feat.getStructure().getChildren()));
			}
			featureList.add(feat);
		}
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		super.inverseOperation();
		// Set the right group types for the features
		for (final IFeature ifeature : andList) {
			if (featureModel.getFeature(ifeature.getName()) != null) {
				featureModel.getFeature(ifeature.getName()).getStructure().changeToAnd();
			}
		}
		for (final IFeature ifeature : alternativeList) {
			if (featureModel.getFeature(ifeature.getName()) != null) {
				featureModel.getFeature(ifeature.getName()).getStructure().changeToAlternative();
			}
		}
		for (final IFeature ifeature : orList) {
			if (featureModel.getFeature(ifeature.getName()) != null) {
				featureModel.getFeature(ifeature.getName()).getStructure().changeToOr();
			}
		}
		return new FeatureIDEEvent(null, EventType.STRUCTURE_CHANGED);
	}

}
