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
package de.ovgu.featureide.ui.views.collaboration.action;

import java.util.LinkedHashSet;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.IStructuredSelection;

import de.ovgu.featureide.ui.views.collaboration.CollaborationView;
import de.ovgu.featureide.ui.views.collaboration.editparts.ClassEditPart;
import de.ovgu.featureide.ui.views.collaboration.editparts.CollaborationEditPart;
import de.ovgu.featureide.ui.views.collaboration.editparts.RoleEditPart;

/**
 * Filters the collaboration model
 * 
 * @author Jens Meinicke
 */
public class FilterAction extends Action {

	private GraphicalViewerImpl viewer;
	private LinkedHashSet<String> classFilter = new LinkedHashSet<String>(); 
	private LinkedHashSet<String> featureFilter = new LinkedHashSet<String>();
	private CollaborationView collaborationView;
	
	public boolean checked = false;
	
	public FilterAction(String text, GraphicalViewerImpl view, CollaborationView collaborationView) {
		super(text);
		this.collaborationView = collaborationView;
		viewer = view;
	}

	public void setEnabled(boolean enabled) {
		IStructuredSelection selection = (IStructuredSelection) viewer.getSelection();
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
	}
	
	@SuppressWarnings("unchecked")
	public void run() {
		if (((classFilter.size() != 0 || featureFilter.size() != 0) && !checked) &&
				collaborationView.builder.classFilter.size() == 0 &&
				collaborationView.builder.featureFilter.size() == 0) {
			setChecked(true);
			checked = true;
			collaborationView.builder.classFilter = (LinkedHashSet<String>) classFilter.clone();
			collaborationView.builder.featureFilter = (LinkedHashSet<String>) featureFilter.clone();
			collaborationView.refresh();
		} else {
			setChecked(false);
			checked = false;
			classFilter.clear();
			featureFilter.clear();
			collaborationView.builder.classFilter.clear();
			collaborationView.builder.featureFilter.clear();
			collaborationView.updateGuiAfterBuild(collaborationView.getFeatureProject(), null);
		}
	}
}
