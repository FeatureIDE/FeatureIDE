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

import org.eclipse.gef.Request;
import org.eclipse.gef.RequestConstants;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConstraintEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;

/**
 * Action to send a selection request when ModelEditParts get selected.
 * 
 * @author Cyrill Meyer
 * @author Eric Schubert
 */
public class SelectionAction extends Action {

	private ISelectionChangedListener listener = new ISelectionChangedListener() {
		public void selectionChanged(SelectionChangedEvent event) {
			IStructuredSelection selection = (IStructuredSelection) event
					.getSelection();

			if (isSelectionValid(selection)){				
				if (selection.getFirstElement() instanceof ConstraintEditPart) {
					for (Constraint constraint : model.getConstraints()) {
						if (constraint.isFeatureSelected()) constraint.setFeatureSelected(false);
					}
					
					((ConstraintEditPart) selection.getFirstElement()).performRequest(new Request(RequestConstants.REQ_SELECTION));
					
					
				} else  if (selection.getFirstElement() instanceof FeatureEditPart){
					for (Feature feature : model.getFeatures()) {
						if (feature.isConstraintSelected()) feature.setConstraintSelected(false);
					}
					
					((FeatureEditPart) selection.getFirstElement()).performRequest(new Request(RequestConstants.REQ_SELECTION));
					
				} else {
					for (Feature feature : model.getFeatures()) {
						if (feature.isConstraintSelected()) feature.setConstraintSelected(false);
					}
					
					for (Constraint constraint : model.getConstraints()) {
						if (constraint.isFeatureSelected()) constraint.setFeatureSelected(false);
					}
				}
			} else {
				for (Feature feature : model.getFeatures()) {
					if (feature.isConstraintSelected()) feature.setConstraintSelected(false);
				}
				
				for (Constraint constraint : model.getConstraints()) {
					if (constraint.isFeatureSelected()) constraint.setFeatureSelected(false);
				}
			}
			
		}
	};
	
	private FeatureModel model;
	
	public SelectionAction (GraphicalViewerImpl viewer, FeatureModel featureModel){
		super("Selection");
		this.model = featureModel;
		
		viewer.addSelectionChangedListener(listener);
	}
	
	public boolean isSelectionValid(IStructuredSelection selection){
		return selection.size() == 1;
	}
	
	
	
	
}
