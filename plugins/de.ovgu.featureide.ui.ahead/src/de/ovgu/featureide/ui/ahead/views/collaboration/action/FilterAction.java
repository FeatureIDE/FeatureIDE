/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.ui.ahead.views.collaboration.action;

import java.util.LinkedList;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.widgets.Display;

import de.ovgu.featureide.ui.ahead.AheadUIPlugin;
import de.ovgu.featureide.ui.ahead.views.collaboration.CollaborationView;
import de.ovgu.featureide.ui.ahead.views.collaboration.editparts.ClassEditPart;
import de.ovgu.featureide.ui.ahead.views.collaboration.editparts.CollaborationEditPart;
import de.ovgu.featureide.ui.ahead.views.collaboration.editparts.RoleEditPart;
import de.ovgu.featureide.ui.ahead.views.collaboration.model.CollaborationModel;

/**
 * Filters the collaboration model
 * 
 * @author Jens Meinicke
 */
public class FilterAction extends Action {

	private GraphicalViewerImpl viewer;
	private LinkedList<String> classFilter ,featureFilter;
	private CollaborationModel model;
	private CollaborationView collaborationView;
	
	public boolean checked = false;
	
	public FilterAction(String text, GraphicalViewerImpl view, CollaborationView collaborationView, CollaborationModel model) {
		super(text);
		this.collaborationView = collaborationView;
		viewer = view;
		this.model = model;
	}

	public void setEnabled(boolean enabled) {
		IStructuredSelection selection = (IStructuredSelection) viewer.getSelection();
		classFilter = new LinkedList<String>();
		featureFilter = new LinkedList<String>();
		super.setEnabled(false);
		
		for (Object part : selection.toList()) {
			if (part instanceof RoleEditPart) { 
				classFilter.add(((RoleEditPart) part).getRoleModel().getName());
				super.setEnabled(true);
			} else if (part instanceof ClassEditPart) {
				classFilter.add(((ClassEditPart) part).getClassModel().getName());
				super.setEnabled(true);
			} else if (part instanceof CollaborationEditPart) {
				featureFilter.add(((CollaborationEditPart) part).getCollaborationModel().getName());
				super.setEnabled(true);
			}
		}
		if (checked) 
			super.setEnabled(true);
//			setChecked(true);
//		} else {
//			setChecked(false);
//		}
	}
	
	public void run() {
		if (classFilter.size() != 0 || featureFilter.size() != 0) {
			super.setChecked(true);
			checked = true;
			collaborationView.builder.setClassFilter(classFilter);
			collaborationView.builder.setFeatureFilter(featureFilter);
			model = collaborationView.builder.buildCollaborationModel(collaborationView.getFeatureProject());
			if (model == null) {
				AheadUIPlugin.getDefault().logInfo("model loading error");
				return;
			}
			Display.getDefault().syncExec(new Runnable(){	
				public void run(){
					viewer.setContents(model);		
					viewer.getContents().refresh();
				}
			});	
		} else {//if (isChecked()) {
			
			super.setChecked(false);
			checked = false;
			classFilter = new LinkedList<String>();
			featureFilter = new LinkedList<String>();
			collaborationView.builder.setClassFilter(classFilter);
			collaborationView.builder.setFeatureFilter(featureFilter);
			collaborationView.updateGuiAfterBuild(collaborationView.getFeatureProject());
		}
	}
}
