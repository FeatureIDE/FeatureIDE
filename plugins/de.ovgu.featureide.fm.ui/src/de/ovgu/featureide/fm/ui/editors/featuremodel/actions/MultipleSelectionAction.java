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

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import org.eclipse.gef.ui.parts.AbstractEditPartViewer;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.impl.Feature;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConnectionEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.views.outline.standard.FmOutlineGroupStateStorage;

/**
 * A default implementation for actions that allow more than one feature to be selected.
 *
 * @author Chico Sundermann
 * @author Paul Westphal
 */
public abstract class MultipleSelectionAction extends AFeatureModelAction implements IEventListener {

	private final ISelectionChangedListener listener = new ISelectionChangedListener() {

		@Override
		public void selectionChanged(SelectionChangedEvent event) {
			final IStructuredSelection selection = (IStructuredSelection) event.getSelection();
			selectionElementChanged(isValidSelection(selection));
		}
	};

	Object viewer;
	protected boolean connectionSelected;
	protected List<String> featureArray;

	/**
	 * Default constructor
	 *
	 * @param text of the action in context menu
	 * @param viewer2 viewer
	 * @param id id
	 */
	public MultipleSelectionAction(String text, Object viewer2, String id, IFeatureModelManager featureModelManager) {
		super(text, id, featureModelManager);
		viewer = viewer2;
		setEnabled(false);
		if (viewer2 instanceof GraphicalViewerImpl) {
			((GraphicalViewerImpl) viewer2).addSelectionChangedListener(listener);
		} else {
			((TreeViewer) viewer2).addSelectionChangedListener(listener);
		}
	}

	/**
	 * returns the selected features as IFeatures
	 *
	 * @return selected IFeature array
	 */
	protected List<String> getSelectedFeatures() {
		final ArrayList<String> features = new ArrayList<>();

		IStructuredSelection selection;
		if (viewer instanceof TreeViewer) {
			selection = (IStructuredSelection) ((TreeViewer) viewer).getSelection();
			for (final Object obj : selection.toArray()) {
				if (obj instanceof FmOutlineGroupStateStorage) {
					features.add(((FmOutlineGroupStateStorage) obj).getFeature().getName());
				} else {
					features.add(((IFeature) obj).getName());
				}
			}
			return features;
		} else {
			selection = (IStructuredSelection) ((AbstractEditPartViewer) viewer).getSelection();
		}

		final Object part = selection.getFirstElement();
		connectionSelected = part instanceof ConnectionEditPart;
		if (connectionSelected) {
			for (final Object obj : selection.toArray()) {
				if (obj instanceof ConnectionEditPart) {
					final IFeature tempFeature = ((ConnectionEditPart) obj).getModel().getTarget().getObject();
					features.add(tempFeature.getName());
				}
			}
			return features;
		} else if (part instanceof FeatureEditPart) {
			for (final Object obj : selection.toArray()) {
				if (obj instanceof FeatureEditPart) {
					features.add(((FeatureEditPart) obj).getModel().getObject().getName());
				}
			}
		}
		return features;
	}

	/**
	 * Is called whenever the selection changes
	 *
	 * @param validSelection
	 */
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
			for (final String name : featureArray) {
				final IFeature feature = featureModel.getFeature(name);
				if (feature != null) {
					feature.addListener(this);
				}
			}
		} else {
			featureArray = null;
		}
	}

	/**
	 * For enabling/disabling the menu entry and the checkbox
	 */
	protected abstract void updateProperties();

	/**
	 * Checks whether selection only contains features and that those features are editable (not external features)
	 *
	 * @param selection
	 * @return boolean indicating whether there are only editable features selected
	 */
	protected boolean isValidSelection(IStructuredSelection selection) {
		for (final Object obj : selection.toArray()) {
			if (!((obj instanceof FeatureEditPart) || (obj instanceof IFeature) || (obj instanceof Feature))) {
				return false;
			}
		}

		// check whether the selection includes no feature from an external submodel
		if ((this instanceof ActionAllowedInExternalSubmodel) || !hasExternalFeature(selection)) {
			return true;
		}

		return false;

	}

	@Override
	public void propertyChange(FeatureIDEEvent event) {
		final EventType prop = event.getEventType();
		if (EventType.GROUP_TYPE_CHANGED.equals(prop) || EventType.MANDATORY_CHANGED.equals(prop) || EventType.PARENT_CHANGED.equals(prop)
			|| EventType.FEATURE_HIDDEN_CHANGED.equals(prop) || EventType.FEATURE_COLOR_CHANGED.equals(prop)
			|| EventType.FEATURE_COLLAPSED_CHANGED.equals(prop)) {
			updateProperties();
		}
	}

	@Override
	protected List<IFeature> getInvolvedFeatures() {
		return getSelectedFeatures().stream().map(f -> featureModelManager.getObject().getFeature(f)).collect(Collectors.toList());
	}

}
