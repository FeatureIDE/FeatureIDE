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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import static de.ovgu.featureide.fm.core.localization.StringTable.COLLAPSE_FEATURE;
import static de.ovgu.featureide.fm.core.localization.StringTable.SET_FEATURES_COLLAPSED;
import static de.ovgu.featureide.fm.core.localization.StringTable.SET_FEATURES_EXPANDED;
import static de.ovgu.featureide.fm.core.localization.StringTable.SET_FEATURE_COLLAPSED;
import static de.ovgu.featureide.fm.core.localization.StringTable.SET_FEATURE_EXPANDED;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.gef.ui.parts.AbstractEditPartViewer;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConnectionEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.SetFeatureToCollapseOperation;
import de.ovgu.featureide.fm.ui.views.outline.standard.FmOutlineGroupStateStorage;

/**
 * collapse the current selected feature
 *
 * @author Joshua Sprey
 * @author Enis Belli
 * @author Chico Sundermann
 * @author Paul Westphal
 */
public class CollapseAction extends MultipleSelectionAction implements ActionAllowedInExternalSubmodel {

	public static final String ID = "de.ovgu.featureide.collapse";
	private final IGraphicalFeatureModel graphicalFeatureModel;
	private IGraphicalFeature[] graphicalFeatureArray;
	private final ISelectionChangedListener listener = new ISelectionChangedListener() {

		@Override
		public void selectionChanged(SelectionChangedEvent event) {
			final IStructuredSelection selection = (IStructuredSelection) event.getSelection();
			if (!isValidSelection(selection)) {
				setEnabled(false);
			}
		}
	};

	public CollapseAction(Object viewer, IGraphicalFeatureModel graphicalFeatureModel) {
		super(COLLAPSE_FEATURE, viewer, ID, graphicalFeatureModel.getFeatureModelManager());
		this.graphicalFeatureModel = graphicalFeatureModel;

		setEnabled(false);
		if (viewer instanceof GraphicalViewerImpl) {
			((GraphicalViewerImpl) viewer).addSelectionChangedListener(listener);
		} else {
			((TreeViewer) viewer).addSelectionChangedListener(listener);
		}
	}

	private boolean isEveryFeatureCollapsed() {
		for (final IGraphicalFeature tempFeature : graphicalFeatureArray) {
			if (!(tempFeature.isCollapsed())) {
				return false;
			}
		}
		return true;
	}

	@Override
	protected void selectionElementChanged(boolean validSelection) {
		final List<String> selectedFeatures = getSelectedFeatures();
		featureModelManager.editObject(featureModel -> addListeners(featureModel, selectedFeatures, validSelection), FeatureModelManager.CHANGE_NOTHING);
		if (validSelection) {
			updateProperties();
		} else {
			setEnabled(false);
		}
	}

	private void addListeners(IFeatureModel featureModel, List<String> newFeatureArray, boolean validSelection) {
		if (featureArray != null) {
			for (final String name : featureArray) {
				final IFeature feature = featureModel.getFeature(name);
				if (feature != null) {
					feature.removeListener(this);
				}
			}
		}
		if (validSelection) {
			featureArray = newFeatureArray;
			final ArrayList<IGraphicalFeature> tempGraphicalFeatureList = new ArrayList<>(featureArray.size());
			for (final String name : featureArray) {
				final IFeature feature = featureModel.getFeature(name);
				if (feature != null) {
					tempGraphicalFeatureList.add(graphicalFeatureModel.getGraphicalFeature(feature));
					feature.addListener(this);
				}
			}
			graphicalFeatureArray = tempGraphicalFeatureList.toArray(new IGraphicalFeature[tempGraphicalFeatureList.size()]);
		} else {
			featureArray = null;
		}
	}

	@Override
	public void run() {
		setChecked(isEveryFeatureCollapsed());
		changeCollapsedStatus(isEveryFeatureCollapsed());
	}

	private void changeCollapsedStatus(boolean allCollapsed) {
		FeatureModelOperationWrapper.run(new SetFeatureToCollapseOperation(featureArray, graphicalFeatureModel, allCollapsed, getStringLabel()));
	}

	private String getStringLabel() {
		if (featureArray.size() == 1) {
			if (isEveryFeatureCollapsed()) {
				return SET_FEATURE_EXPANDED;
			} else {
				return SET_FEATURE_COLLAPSED;
			}
		} else {
			if (isEveryFeatureCollapsed()) {
				return SET_FEATURES_EXPANDED;
			} else {
				return SET_FEATURES_COLLAPSED;
			}
		}
	}

	@Override
	protected void updateProperties() {
		setEnabled(isThereAtLeastOneFeatureThatHasChildren());
		// Box is not checked if the action is disabled
		if (!isThereAtLeastOneFeatureThatHasChildren()) {
			setChecked(false);
		} else {
			setChecked(isEveryFeatureCollapsed());
		}
	}

	private boolean isThereAtLeastOneFeatureThatHasChildren() {
		final IFeatureModel featureModel = featureModelManager.getSnapshot();
		for (final String name : featureArray) {
			final IFeature feature = featureModel.getFeature(name);
			if (feature.getStructure().hasChildren()) {
				return true;
			}
		}
		return false;
	}

	// Modified getSelectedFeatures() so that only features with children are included
	@Override
	protected List<String> getSelectedFeatures() {
		final ArrayList<String> features = new ArrayList<>();

		IStructuredSelection selection;
		if (viewer instanceof TreeViewer) {
			selection = (IStructuredSelection) ((TreeViewer) viewer).getSelection();
			if (selection.getFirstElement() instanceof FmOutlineGroupStateStorage) {
				for (final Object obj : selection.toArray()) {
					if (((FmOutlineGroupStateStorage) obj).getFeature().getStructure().hasChildren()) {
						features.add(((FmOutlineGroupStateStorage) obj).getFeature().getName());
					}
				}
				return features;
			} else {
				for (final Object obj : selection.toArray()) {
					if (((IFeature) obj).getStructure().hasChildren()) {
						features.add(((IFeature) obj).getName());
					}
				}
				return features;
			}
		} else {
			selection = (IStructuredSelection) ((AbstractEditPartViewer) viewer).getSelection();
		}

		final Object part = selection.getFirstElement();
		connectionSelected = part instanceof ConnectionEditPart;
		if (connectionSelected) {
			for (final Object obj : selection.toArray()) {
				if (obj instanceof ConnectionEditPart) {
					final IFeature tempFeature = ((ConnectionEditPart) obj).getModel().getTarget().getObject();
					if (tempFeature.getStructure().hasChildren()) {
						features.add(tempFeature.getName());
					}
				}
			}
			return features;
		} else if (part instanceof FeatureEditPart) {
			for (final Object obj : selection.toArray()) {
				if (obj instanceof FeatureEditPart) {
					final IFeature feature = ((FeatureEditPart) obj).getModel().getObject();
					if (feature.getStructure().hasChildren()) {
						features.add(feature.getName());
					}
				}
			}
		}
		return features;
	}
}
