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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE_INCLUDING_SUBFEATURES;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureTreeDeleteOperation;

/**
 * Action to delete a single feature including its sub features
 *
 * @author Jan Wedding
 * @author Melanie Pflaume
 * @author Marcus Pinnecke (Feature Interface)
 * @author Chico Sundermann
 * @author Paul Westphal
 */
public class DeleteAllAction extends MultipleSelectionAction {

	public static final String ID = "de.ovgu.featureide.deleteall";
	private static ImageDescriptor deleteImage = PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_TOOL_DELETE);

	/**
	 *
	 * @param viewer View that calls this action
	 * @param featureModel respective feature model
	 */
	public DeleteAllAction(Object viewer, IFeatureModelManager featureModelManager) {
		super(DELETE_INCLUDING_SUBFEATURES, viewer, ID, featureModelManager);
		setImageDescriptor(deleteImage);
	}

	@Override
	public void run() {
		FeatureModelOperationWrapper.run(new FeatureTreeDeleteOperation(featureModelManager, getParentsFromSelectedFeatures()));
	}

	@Override
	protected void updateProperties() {
		setEnabled(!selectedFeaturesContainRoot());
	}

	private boolean selectedFeaturesContainRoot() {
		final IFeatureModel featureModel = featureModelManager.editObject();
		for (final String name : featureArray) {
			final IFeature tempFeature = featureModel.getFeature(name);
			if (tempFeature.getStructure().isRoot()) {
				return true;
			}
		}
		return false;
	}

	private List<String> getParentsFromSelectedFeatures() {
		final ArrayList<String> parents = new ArrayList<>();
		final IFeatureModel featureModel = featureModelManager.editObject();
		for (final String name : featureArray) {
			if (!hasParentsInTheSubTree(featureModel.getFeature(name))) {
				parents.add(name);
			}
		}
		return parents;
	}

	private boolean hasParentsInTheSubTree(IFeature feature) {
		final IFeatureModel featureModel = featureModelManager.editObject();
		for (final String name : featureArray) {
			final IFeature temp = featureModel.getFeature(name);
			if (feature.getStructure().isAncestorOf(temp.getStructure())) {
				return true;
			}
		}
		return false;
	}
}
