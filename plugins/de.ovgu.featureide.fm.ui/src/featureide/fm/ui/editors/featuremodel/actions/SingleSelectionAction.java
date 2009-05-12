/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package featureide.fm.ui.editors.featuremodel.actions;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;

import featureide.fm.core.Feature;
import featureide.fm.core.PropertyConstants;
import featureide.fm.ui.editors.featuremodel.editparts.ConnectionEditPart;
import featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;

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
			IStructuredSelection selection = (IStructuredSelection) event.getSelection();
			SingleSelectionAction.this
					.selectionChanged(isValidSelection(selection));
		}
	};

	GraphicalViewerImpl viewer;

	protected Feature feature;
	
	protected boolean connectionSelected;

	public SingleSelectionAction(String text, GraphicalViewerImpl viewer) {
		super(text);
		this.viewer = viewer;
		setEnabled(false);
		viewer.addSelectionChangedListener(listener);
	}

	private boolean isOneFeatureSelected(IStructuredSelection selection) {
		return selection.size() == 1
				&& (selection.getFirstElement() instanceof FeatureEditPart || selection
						.getFirstElement() instanceof ConnectionEditPart);
	}

	public Feature getSelectedFeature() {
		IStructuredSelection selection = (IStructuredSelection) viewer
				.getSelection();
		Object part = selection.getFirstElement();
		connectionSelected = part instanceof ConnectionEditPart;
		if (connectionSelected)
			return ((ConnectionEditPart) part).getConnectionModel().getTarget();
		return ((FeatureEditPart) part).getFeatureModel();
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
		if (prop.equals(CHILDREN_CHANGED) || prop.equals(MANDANTORY_CHANGED)
				|| prop.equals(PARENT_CHANGED)) {
			updateProperties();
		}
	}

}
