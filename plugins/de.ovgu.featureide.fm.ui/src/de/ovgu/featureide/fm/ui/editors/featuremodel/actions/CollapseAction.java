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

import static de.ovgu.featureide.fm.core.localization.StringTable.COLLAPSE_FEATURE;
import static de.ovgu.featureide.fm.core.localization.StringTable.SET_FEATURES_COLLAPSED;
import static de.ovgu.featureide.fm.core.localization.StringTable.SET_FEATURES_EXPANDED;
import static de.ovgu.featureide.fm.core.localization.StringTable.SET_FEATURE_COLLAPSED;
import static de.ovgu.featureide.fm.core.localization.StringTable.SET_FEATURE_EXPANDED;

import java.util.ArrayList;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.gef.ui.parts.AbstractEditPartViewer;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConnectionEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
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
public class CollapseAction extends MultipleSelectionAction {

	public static final String ID = "de.ovgu.featureide.collapse";
	private final IGraphicalFeatureModel graphicalFeatureModel;
	private IFeature[] featureArray;
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
		super(COLLAPSE_FEATURE, viewer, ID);
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

	private void refreshGraphicalFeatures() {
		final ArrayList<IGraphicalFeature> tempGraphicalFeatureList = new ArrayList<>();

		for (final IFeature tempFeature : featureArray) {
			tempGraphicalFeatureList.add(graphicalFeatureModel.getGraphicalFeature(tempFeature));
		}

		graphicalFeatureArray = tempGraphicalFeatureList.toArray(new IGraphicalFeature[tempGraphicalFeatureList.size()]);
	}

	@Override
	protected void selectionElementChanged(boolean validSelection) {
		if (featureArray != null) {
			for (final Object obj : featureArray) {
				((IFeature) obj).removeListener(this);
			}
		}
		if (validSelection) {
			featureArray = getSelectedFeatures();
			refreshGraphicalFeatures();
			for (final IFeature tempFeature : featureArray) {
				tempFeature.addListener(this);
			}
			updateProperties();
		} else {
			featureArray = null;
			setEnabled(false);
		}
	}

	@Override
	public void run() {
		setChecked(isEveryFeatureCollapsed());
		changeCollapsedStatus(isEveryFeatureCollapsed());
	}

	private void changeCollapsedStatus(boolean allCollapsed) {
		final SetFeatureToCollapseOperation op = new SetFeatureToCollapseOperation(featureArray, graphicalFeatureModel, allCollapsed, getStringLabel());

		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
		} catch (final ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);

		}
	}

	private String getStringLabel() {
		if (featureArray.length == 1) {
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
		for (final IFeature tempFeature : featureArray) {
			if (tempFeature.getStructure().hasChildren()) {
				return true;
			}
		}
		return false;
	}

	// Modified getSelectedFeatures() so that only features with children are included
	@Override
	protected IFeature[] getSelectedFeatures() {
		final ArrayList<IFeature> features = new ArrayList<>();

		IStructuredSelection selection;
		if (viewer instanceof TreeViewer) {
			selection = (IStructuredSelection) ((TreeViewer) viewer).getSelection();
			if (selection.getFirstElement() instanceof FmOutlineGroupStateStorage) {
				for (final Object obj : selection.toArray()) {
					if (((FmOutlineGroupStateStorage) obj).getFeature().getStructure().hasChildren()) {
						features.add(((FmOutlineGroupStateStorage) obj).getFeature());
					}
				}
				return features.toArray(new IFeature[features.size()]);
			} else {
				for (final Object obj : selection.toArray()) {
					if (((IFeature) obj).getStructure().hasChildren()) {
						features.add((IFeature) obj);
					}
				}
				return features.toArray(new IFeature[features.size()]);
			}
		} else {
			selection = (IStructuredSelection) ((AbstractEditPartViewer) viewer).getSelection();
		}

		final Object part = selection.getFirstElement();
		connectionSelected = part instanceof ConnectionEditPart;
		if (connectionSelected) {
			for (final Object obj : selection.toArray()) {
				final IFeature tempFeature = ((ConnectionEditPart) obj).getModel().getTarget().getObject();
				if (tempFeature.getStructure().hasChildren()) {
					features.add(tempFeature);
				}
			}
			return features.toArray(new IFeature[features.size()]);
		}
		for (final Object obj : selection.toArray()) {
			if (((FeatureEditPart) obj).getModel().getObject().getStructure().hasChildren()) {
				features.add(((FeatureEditPart) obj).getModel().getObject());
			}
		}
		return features.toArray(new IFeature[features.size()]);
	}

}
