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

import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE;
import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE_ERROR;
import static de.ovgu.featureide.fm.core.localization.StringTable.UNABLE_TO_DELETE_THIS_FEATURES_UNTIL_ALL_RELEVANT_CONSTRAINTS_ARE_REMOVED_;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureModelOperationEvent;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
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

	public static final String ID = ID_PREFIX + "SetFeatureToAbstractOperation";

	private final LinkedList<String> andList = new LinkedList<>();
	private final LinkedList<String> orList = new LinkedList<>();
	private final LinkedList<String> alternativeList = new LinkedList<>();

	public FeatureTreeDeleteOperation(IFeatureModelManager featureModelManager, List<String> parents) {
		super(featureModelManager, DELETE, parents);
	}

	@Override
	protected String getID() {
		return ID;
	}

	@Override
	protected void createSingleOperations(IFeatureModel featureModel) {
		andList.clear();
		alternativeList.clear();
		orList.clear();
		for (final String name : featureNames) {
			final List<IFeature> featureList = new LinkedList<>();
			final List<IFeature> containedFeatureList = new LinkedList<>();
			getFeaturesToDelete(Arrays.asList(featureModel.getFeature(name)), featureList, containedFeatureList);

			if (containedFeatureList.isEmpty()) {
				for (final IFeature feat : featureList) {
					final String delFeatureName = feat.getName();
					if (feat.getStructure().isAnd()) {
						andList.add(delFeatureName);
					} else if (feat.getStructure().isOr()) {
						orList.add(delFeatureName);
					} else if (feat.getStructure().isAlternative()) {
						alternativeList.add(delFeatureName);
					}
					final AbstractFeatureModelOperation op = new DeleteFeatureOperation(featureModelManager, delFeatureName);
					operations.add(op);
				}
			} else {
				final String containedFeatures = containedFeatureList.toString();
				final MessageDialog dialog = new MessageDialog(new Shell(), DELETE_ERROR, FEATURE_SYMBOL,
						"The following features are contained in constraints:" + '\n' + containedFeatures.substring(1, containedFeatures.length() - 1) + '\n'
							+ '\n' + UNABLE_TO_DELETE_THIS_FEATURES_UNTIL_ALL_RELEVANT_CONSTRAINTS_ARE_REMOVED_,
						MessageDialog.ERROR, new String[] { IDialogConstants.OK_LABEL }, 0);

				dialog.open();
			}
		}
	}

	private void getFeaturesToDelete(List<IFeature> features, List<IFeature> deleteFeatureList, List<IFeature> containedFeatureList) {
		for (final IFeature feat : features) {
			if (!feat.getStructure().getRelevantConstraints().isEmpty()) {
				containedFeatureList.add(feat);
			}
			if (feat.getStructure().hasChildren()) {
				getFeaturesToDelete(FeatureUtils.convertToFeatureList(feat.getStructure().getChildren()), deleteFeatureList, containedFeatureList);
			}
			deleteFeatureList.add(feat);
		}
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final FeatureModelOperationEvent event = (FeatureModelOperationEvent) super.inverseOperation(featureModel);
		// Set the right group types for the features
		for (final String name : andList) {
			final IFeature feature = featureModel.getFeature(name);
			if (featureModel.getFeature(feature.getName()) != null) {
				featureModel.getFeature(feature.getName()).getStructure().changeToAnd();
			}
		}
		for (final String name : alternativeList) {
			final IFeature feature = featureModel.getFeature(name);
			if (featureModel.getFeature(feature.getName()) != null) {
				featureModel.getFeature(feature.getName()).getStructure().changeToAlternative();
			}
		}
		for (final String name : orList) {
			final IFeature feature = featureModel.getFeature(name);
			if (featureModel.getFeature(feature.getName()) != null) {
				featureModel.getFeature(feature.getName()).getStructure().changeToOr();
			}
		}
		return event;
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_DEPENDENCIES;
	}

}
