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
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import static de.ovgu.featureide.fm.core.localization.StringTable.HIDE_OPERATION;

import java.util.ArrayList;

import org.eclipse.gef.ui.parts.AbstractEditPartViewer;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.Feature;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConnectionEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.views.outline.standard.FmOutlineGroupStateStorage;

/**
 * Operation with functionality to set Features hidden. Enables undo/redo functionality.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 * @author Paul Westphal
 * @author Chico Sundermann
 */
public class SetFeatureToHiddenOperation extends MultiFeatureModelOperation {

	private final Object viewer;
	private final boolean allHidden;
	private boolean connectionSelected;

	public SetFeatureToHiddenOperation(Object viewer, IFeatureModel featureModel, boolean allHidden) {
		super(featureModel, HIDE_OPERATION);
		this.viewer = viewer;
		this.allHidden = allHidden;
	}

	private IStructuredSelection getSelection() {
		if (viewer instanceof GraphicalViewerImpl) {
			return (IStructuredSelection) ((GraphicalViewerImpl) viewer).getSelection();
		} else {
			return (IStructuredSelection) ((TreeViewer) viewer).getSelection();
		}
	}
	
	/*private IFeature[] getSelectedFeatures() {
		ArrayList<IFeature> features = new ArrayList<>();
		IStructuredSelection selection;
		
		if (viewer instanceof GraphicalViewerImpl) {
			selection = (IStructuredSelection) ((GraphicalViewerImpl) viewer).getSelection();
			for (Object obj : selection.toArray()) {
				if (obj instanceof FeatureEditPart) {
					features.add(((FeatureEditPart) obj).getModel().getObject());
				}
			}
		} if (viewer instanceof TreeViewer) {
			selection = (IStructuredSelection) ((TreeViewer) viewer).getSelection();
			Feature tempf = null;
			for (Object obj : selection.toArray()) {
				if (obj instanceof Feature) {
					tempf = (Feature)obj;
					break;
				}
			}
			if (tempf != null) {
				for (Object obj : tempf.getFeatureModel().getFeatures()) {
					features.add((IFeature)obj);
				}
			}
		}
		return features.toArray(new IFeature[features.size()]);
	}*/
	
	public IFeature getSelectedFeatures() {
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
	

	@Override
	protected void createSingleOperations() {
		// TODO UNTERSCHEIDEN ZWISCHEN FEATUREEDITPART UND FEATURE
		for (Object obj : getSelection().toArray()) {
			IFeature tempFeature = ((FeatureEditPart) obj).getModel().getObject();
			if(allHidden || !tempFeature.getStructure().isHidden()) {
				final HideFeatureOperation op = new HideFeatureOperation(tempFeature, featureModel);
				operations.add(op);
			}
		}		
	}

}