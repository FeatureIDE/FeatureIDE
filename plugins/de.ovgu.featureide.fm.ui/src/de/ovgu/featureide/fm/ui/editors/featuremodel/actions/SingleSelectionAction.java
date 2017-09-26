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
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConnectionEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.views.outline.standard.FmOutlineGroupStateStorage;

/**
 * A default implementation for actions that only allow one feature to be selected.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke
 */
public abstract class SingleSelectionAction extends Action implements IEventListener {

	private final ISelectionChangedListener listener = new ISelectionChangedListener() {

		@Override
		public void selectionChanged(SelectionChangedEvent event) {
			final IStructuredSelection selection = (IStructuredSelection) event.getSelection();
			selectionElementChanged(isValidSelection(selection));
		}
	};

	Object viewer;

	protected IFeature feature;

	protected boolean connectionSelected;

	public SingleSelectionAction(String text, Object viewer2) {
		super(text);
		viewer = viewer2;
		setEnabled(false);
		if (viewer2 instanceof GraphicalViewerImpl) {
			((GraphicalViewerImpl) viewer2).addSelectionChangedListener(listener);
		} else {
			((TreeViewer) viewer2).addSelectionChangedListener(listener);
		}
	}

	private boolean isOneFeatureSelected(IStructuredSelection selection) {
		return (selection.size() == 1)
			&& ((selection.getFirstElement() instanceof FeatureEditPart) || (selection.getFirstElement() instanceof ConnectionEditPart)
				|| (selection.getFirstElement() instanceof FmOutlineGroupStateStorage) || (selection.getFirstElement() instanceof IFeature));
	}

	public FeatureEditPart getSelectedFeatureEditPart(Object diagramEditor) {
		Object part;
		if (diagramEditor == null) {
			final IStructuredSelection selection = (IStructuredSelection) ((AbstractEditPartViewer) viewer).getSelection();
			part = selection.getFirstElement();
		} else {
			final IFeature selection = (IFeature) ((IStructuredSelection) ((TreeViewer) viewer).getSelection()).getFirstElement();
			part = ((GraphicalViewerImpl) diagramEditor).getEditPartRegistry().get(selection);
		}

		connectionSelected = part instanceof ConnectionEditPart;

		if (connectionSelected) {
			return ((ConnectionEditPart) part).getTarget();
		} else {
			return (FeatureEditPart) part;
		}
	}

	public IFeature getSelectedFeature() {
		IStructuredSelection selection;
		if (viewer instanceof TreeViewer) {
			selection = (IStructuredSelection) ((TreeViewer) viewer).getSelection();
			if (selection.getFirstElement() instanceof FmOutlineGroupStateStorage) {
				return ((FmOutlineGroupStateStorage) selection.getFirstElement()).getFeature();
			} else {
				return (IFeature) selection.getFirstElement();
			}
		} else {
			selection = (IStructuredSelection) ((AbstractEditPartViewer) viewer).getSelection();
		}

		final Object part = selection.getFirstElement();
		connectionSelected = part instanceof ConnectionEditPart;
		if (connectionSelected) {
			return ((ConnectionEditPart) part).getModel().getTarget().getObject();
		}
		return ((FeatureEditPart) part).getModel().getObject();
	}

	private void selectionElementChanged(boolean oneSelected) {
		if (feature != null) {
			feature.removeListener(this);
		}
		if (oneSelected) {
			feature = getSelectedFeature();
			feature.addListener(this);
			updateProperties();
		} else {
			feature = null;
			setEnabled(false);
			setChecked(false);
		}
	}

	protected boolean isValidSelection(IStructuredSelection selection) {
		return isOneFeatureSelected(selection);
	}

	protected abstract void updateProperties();

	@Override
	public void propertyChange(FeatureIDEEvent event) {
		final EventType prop = event.getEventType();
		if (EventType.GROUP_TYPE_CHANGED.equals(prop) || EventType.MANDATORY_CHANGED.equals(prop) || EventType.PARENT_CHANGED.equals(prop)
			|| EventType.HIDDEN_CHANGED.equals(prop) || EventType.COLOR_CHANGED.equals(prop) || EventType.COLLAPSED_CHANGED.equals(prop)) {
			updateProperties();
		}
	}

	public boolean isConnectionSelected() {
		return connectionSelected;
	}

}
