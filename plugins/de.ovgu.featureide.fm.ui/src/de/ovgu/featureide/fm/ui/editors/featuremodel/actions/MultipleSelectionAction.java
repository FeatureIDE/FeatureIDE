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

import java.util.ArrayList;

import org.eclipse.gef.ui.parts.AbstractEditPartViewer;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.impl.Feature;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConnectionEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.views.outline.standard.FmOutlineGroupStateStorage;

/**
 * A default implementation for actions that allow more than one feature to be selected.
 *
 * @author Chico Sundermann
 * @author Paul Westphal
 */
public abstract class MultipleSelectionAction extends Action implements IEventListener {

	private final ISelectionChangedListener listener = new ISelectionChangedListener() {
		@Override
		public void selectionChanged(SelectionChangedEvent event) {
			final IStructuredSelection selection = (IStructuredSelection) event.getSelection();
			selectionElementChanged(isValidSelection(selection));
		}
	};

	Object viewer;
	protected boolean connectionSelected;
	protected IFeature[] featureArray;

	/**
	 * Default constructor
	 * 
	 * @param text of the action in context menu
	 * @param viewer2
	 */
	public MultipleSelectionAction(String text, Object viewer2, String id) {
		super(text);
		viewer = viewer2;
		setEnabled(false);
		setId(id);
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
	protected IFeature[] getSelectedFeatures() {
		final ArrayList<IFeature> features = new ArrayList<>();

		IStructuredSelection selection;
		if (viewer instanceof TreeViewer) {
			selection = (IStructuredSelection) ((TreeViewer) viewer).getSelection();
			if (selection.getFirstElement() instanceof FmOutlineGroupStateStorage) {
				for (final Object obj : selection.toArray()) {
					features.add(((FmOutlineGroupStateStorage) obj).getFeature());
				}
				return features.toArray(new IFeature[features.size()]);
			} else {
				for (final Object obj : selection.toArray()) {
					features.add((IFeature) obj);
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
				features.add(tempFeature);
			}
			return features.toArray(new IFeature[features.size()]);
		}
		for (final Object obj : selection.toArray()) {
			features.add(((FeatureEditPart) obj).getModel().getObject());
		}
		return features.toArray(new IFeature[features.size()]);
	}

	/**
	 * Is called whenever the selection changes
	 * 
	 * @param validSelection
	 */
	protected void selectionElementChanged(boolean validSelection) {
		if (featureArray != null) {
			for (final Object obj : featureArray) {
				((IFeature) obj).removeListener(this);
			}
		}
		if (validSelection) {
			featureArray = getSelectedFeatures();
			for (final IFeature tempFeature : featureArray) {
				tempFeature.addListener(this);
			}
			updateProperties();
		} else {
			featureArray = null;
			setEnabled(false);
		}
	}

	/**
	 * For enabling/disabling the menu entry and the checkbox
	 */
	protected abstract void updateProperties();

	/**
	 * Checks whether selection only contains features
	 * 
	 * @param selection
	 * @return boolean indicating whether there are only features selected
	 */
	protected boolean isValidSelection(IStructuredSelection selection) {
		for (final Object obj : selection.toArray()) {
			if (!((obj instanceof FeatureEditPart) || (obj instanceof IFeature) || (obj instanceof Feature))) {
				return false;
			}
		}
		return true;
	}

	@Override
	public void propertyChange(FeatureIDEEvent event) {
		final EventType prop = event.getEventType();
		if (EventType.GROUP_TYPE_CHANGED.equals(prop) || EventType.MANDATORY_CHANGED.equals(prop) || EventType.PARENT_CHANGED.equals(prop)
			|| EventType.HIDDEN_CHANGED.equals(prop) || EventType.COLOR_CHANGED.equals(prop) || EventType.COLLAPSED_CHANGED.equals(prop)) {
			updateProperties();
		}
	}

}
