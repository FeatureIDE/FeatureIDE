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

import static de.ovgu.featureide.fm.core.localization.StringTable.AUTO_LAYOUT_LEGEND;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;

import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.LegendEditPart;

/**
 * Switches auto-layout function for the feature model legend.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class LegendLayoutAction extends Action {

	public static final String ID = "de.ovgu.featureide.legendlayout";

	private final IGraphicalFeatureModel featureModel;

	private final ISelectionChangedListener listener = new ISelectionChangedListener() {

		@Override
		public void selectionChanged(SelectionChangedEvent event) {
			final IStructuredSelection selection = (IStructuredSelection) event.getSelection();
			setEnabled(isValidSelection(selection));
		}
	};

	public LegendLayoutAction(GraphicalViewerImpl viewer, IGraphicalFeatureModel featuremodel) {
		super(AUTO_LAYOUT_LEGEND);
		featureModel = featuremodel;
		setId(ID);
		setEnabled(false);
		setChecked(true);
		viewer.addSelectionChangedListener(listener);
	}

	protected boolean isValidSelection(IStructuredSelection selection) {
		if (selection.size() != 1) {
			return false;
		}
		if (selection.getFirstElement() instanceof LegendEditPart) {
			return true;
		} else {
			return false;
		}
	}

	@Override
	public void run() {
		super.run();
		if (featureModel.getLayout().hasLegendAutoLayout()) {
			featureModel.getLayout().setLegendAutoLayout(false);
			setChecked(false);
		} else {
			featureModel.getLayout().setLegendAutoLayout(true);
			setChecked(true);
			featureModel.getFeatureModel().handleModelDataChanged();
		}

	}

	public void refresh() {
		if (featureModel.getLayout().hasLegendAutoLayout()) {
			setChecked(true);
		} else {
			setChecked(false);

		}
	}
}
