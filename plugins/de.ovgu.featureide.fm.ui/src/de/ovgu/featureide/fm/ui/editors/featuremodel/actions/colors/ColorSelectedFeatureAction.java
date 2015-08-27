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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions.colors;

import static de.ovgu.featureide.fm.core.localization.StringTable.COLORATION;

import java.util.ArrayList;

import org.eclipse.core.resources.IProject;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;

/**
 * ColorSelectedFeatureAction is the action that opens the ColorSelectedFeatureDialog
 * with the selected features in the feature diagram.
 * 
 * @author Christian Elzholz, Marcus Schmelz
 */
public class ColorSelectedFeatureAction extends Action {

	protected ArrayList<Feature> featureList = new ArrayList<Feature>();
	final protected Shell shell = new Shell();
	TreeViewer viewer;

	public ISelectionChangedListener listener = new ISelectionChangedListener() {
		public void selectionChanged(SelectionChangedEvent event) {

			IStructuredSelection selection = (IStructuredSelection) event.getSelection();
			updateFeatureList(selection);
			if (featureList.isEmpty()) {
				ColorSelectedFeatureAction.this.setEnabled(false);
			} else {
				ColorSelectedFeatureAction.this.setEnabled(true);
			}
		}

	};

	/**
	 * @param viewer
	 * @param project
	 */
	public ColorSelectedFeatureAction(FeatureDiagramEditor viewer, IProject project) {
		super(COLORATION);
		if (viewer instanceof GraphicalViewerImpl)
			((GraphicalViewerImpl) viewer).addSelectionChangedListener(listener);

	}

	/**
	 * @param selection
	 * Creates a featureList with the selected features of the featurediagram.
	 */
	public void updateFeatureList(IStructuredSelection selection) {

		if (!selection.isEmpty()) {
			featureList.clear();

			Object[] editPartArray = selection.toArray();
			
			for (int i = 0; i < selection.size(); i++) {
				Object editPart = editPartArray[i];
				if (editPart instanceof FeatureEditPart) {
					FeatureEditPart editP = (FeatureEditPart) editPart;
					Feature feature = editP.getFeature();
					if (!featureList.contains(feature))
						featureList.add(feature);
				}
			}
			return;
		} else {
			return;
		}
	}

	public void run() {

		ColorSelectedFeatureDialog dialog = new ColorSelectedFeatureDialog(shell, this.featureList);
		int returnstat = dialog.open();

		if (!featureList.isEmpty() && Window.OK == returnstat) {
			featureList.get(0).getFeatureModel().redrawDiagram();
		}
	}
}
