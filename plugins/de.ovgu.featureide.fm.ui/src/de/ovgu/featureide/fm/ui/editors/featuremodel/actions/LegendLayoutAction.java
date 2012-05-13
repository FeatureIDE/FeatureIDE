/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.LegendEditPart;

/**
 * 
 *   
 * @author Fabian Benduhn
 */
public class LegendLayoutAction extends Action {

	private FeatureModel featureModel;
	private ISelectionChangedListener listener = new ISelectionChangedListener() {
		public void selectionChanged(SelectionChangedEvent event) {
			IStructuredSelection selection = (IStructuredSelection) event
					.getSelection();
			setEnabled(isValidSelection(selection));
		}
	};

	public LegendLayoutAction(GraphicalViewerImpl viewer,
			FeatureModel featuremodel) {
		super("Auto-Layout Legend");
		this.featureModel = featuremodel;
		this.setEnabled(false);
		this.setChecked(true);
		viewer.addSelectionChangedListener(listener);
	}

	protected boolean isValidSelection(IStructuredSelection selection) {
		if (selection.size() != 1)
			return false;
		if (selection.getFirstElement() instanceof LegendEditPart)
			return true;

		else
			return false;
	}

	@Override
	public void run() {
		super.run();
		if (featureModel.getLayout().hasLegendAutoLayout()) {
			featureModel.getLayout().setLegendAutoLayout(false);
			this.setChecked(false);
		} else {
			featureModel.getLayout().setLegendAutoLayout(true);
			this.setChecked(true);
			featureModel.handleModelDataChanged();
		}

	}

	public void refresh() {
		if (featureModel.getLayout().hasLegendAutoLayout()) {
			this.setChecked(true);
		} else {
			this.setChecked(false);

		}
	}
}
