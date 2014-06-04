/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.gef.ui.parts.AbstractEditPartViewer;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConnectionEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.views.outline.FmOutlineGroupStateStorage;

/**
 * A default implementation for actions that only allow one feature to be
 * selected.
 * 
 * @author Thomas Thuem
 */
public abstract class SingleSelectionAction extends Action implements
		PropertyChangeListener, PropertyConstants {

	private ISelectionChangedListener listener = new ISelectionChangedListener() {
		public void selectionChanged(SelectionChangedEvent event) {
			IStructuredSelection selection = (IStructuredSelection) event
					.getSelection();
			SingleSelectionAction.this
					.selectionChanged(isValidSelection(selection));
		}
	};

	Object viewer;

	protected Feature feature;

	protected boolean connectionSelected;

	public SingleSelectionAction(String text, Object viewer2) {
		super(text);
		this.viewer = viewer2;
		setEnabled(false);
		if (viewer2 instanceof GraphicalViewerImpl)
			((GraphicalViewerImpl) viewer2).addSelectionChangedListener(listener);
		else
			((TreeViewer) viewer2).addSelectionChangedListener(listener);
	}

	private boolean isOneFeatureSelected(IStructuredSelection selection) {
		return selection.size() == 1
				&& (selection.getFirstElement() instanceof FeatureEditPart || selection
						.getFirstElement() instanceof ConnectionEditPart || selection
						.getFirstElement() instanceof FmOutlineGroupStateStorage|| selection
						.getFirstElement() instanceof Feature);
	}

	public FeatureEditPart getSelectedFeatureEditPart(Object diagramEditor) {
		Object part;
		if (diagramEditor == null) {
			IStructuredSelection selection = (IStructuredSelection) ((AbstractEditPartViewer) viewer)
					.getSelection();
			part = selection.getFirstElement(); 
		} else {
			Feature selection = (Feature) ((IStructuredSelection) ((TreeViewer) viewer)
					.getSelection()).getFirstElement();
			part = ((GraphicalViewerImpl) diagramEditor).getEditPartRegistry().get(selection);
		}
		
		connectionSelected = part instanceof ConnectionEditPart;
		
		if (connectionSelected)
			return (FeatureEditPart) ((ConnectionEditPart) part).getTarget();
		else
			return (FeatureEditPart) part;
	}

	public Feature getSelectedFeature() {
		IStructuredSelection selection;
		if (viewer instanceof TreeViewer) {
			selection = (IStructuredSelection) ((TreeViewer) viewer).getSelection();
			if (selection.getFirstElement() instanceof FmOutlineGroupStateStorage)
				return ((FmOutlineGroupStateStorage) selection.getFirstElement()).getFeature();
			else
				return (Feature) selection.getFirstElement();
		} else {
			selection = (IStructuredSelection) ((AbstractEditPartViewer) viewer)
				.getSelection();
		}
		
		Object part = selection.getFirstElement();
		connectionSelected = part instanceof ConnectionEditPart;
		if (connectionSelected)
			return ((ConnectionEditPart) part).getConnectionModel().getTarget();
		return ((FeatureEditPart) part).getFeature();
	}

	private void selectionChanged(boolean oneSelected) {
		if (feature != null)
			feature.removeListener(this);
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

	public void propertyChange(PropertyChangeEvent event) {
		String prop = event.getPropertyName();
		if (CHILDREN_CHANGED.equals(prop) || MANDATORY_CHANGED.equals(prop)
				|| PARENT_CHANGED.equals(prop) || HIDDEN_CHANGED.equals(prop) || 
				COLOR_CHANGED.equals(prop)) {
			updateProperties();
		}
	}
	
	public boolean isConnectionSelected() {
		return connectionSelected;
	}

}
