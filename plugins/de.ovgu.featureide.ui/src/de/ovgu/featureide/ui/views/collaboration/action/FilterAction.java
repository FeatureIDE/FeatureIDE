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
package de.ovgu.featureide.ui.views.collaboration.action;

import java.util.HashSet;
import java.util.Set;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.IStructuredSelection;

import de.ovgu.featureide.ui.views.collaboration.CollaborationView;
import de.ovgu.featureide.ui.views.collaboration.editparts.ClassEditPart;
import de.ovgu.featureide.ui.views.collaboration.editparts.CollaborationEditPart;
import de.ovgu.featureide.ui.views.collaboration.editparts.RoleEditPart;
import de.ovgu.featureide.ui.views.collaboration.model.CollaborationModelBuilder;

/**
 * Filters the collaboration model
 *
 * @author Jens Meinicke
 */
public class FilterAction extends Action {

	private final GraphicalViewerImpl viewer;
	private final CollaborationView collaborationView;

	private final Set<String> classFilter = new HashSet<String>();
	private final Set<String> featureFilter = new HashSet<String>();

	public FilterAction(String text, GraphicalViewerImpl view, CollaborationView collaborationView) {
		super(text);
		this.collaborationView = collaborationView;
		viewer = view;
	}

	@Override
	public void setEnabled(boolean enabled) {
		final IStructuredSelection selection = (IStructuredSelection) viewer.getSelection();
		super.setEnabled(false);

		for (final Object part : selection.toList()) {
			if (part instanceof RoleEditPart) {
				classFilter.add(((RoleEditPart) part).getRoleModel().getClassFragment().getName());
				super.setEnabled(true);
			} else if (part instanceof ClassEditPart) {
				classFilter.add(((ClassEditPart) part).getClassModel().getName());
				super.setEnabled(true);
			} else if (part instanceof CollaborationEditPart) {
				featureFilter.add(((CollaborationEditPart) part).getCollaborationModel().getName());
				super.setEnabled(true);
			}
		}
		final boolean filterDefined = CollaborationModelBuilder.isFilterDefined();
		setChecked(filterDefined);
		if (filterDefined) {
			super.setEnabled(true);
		}
	}

	@Override
	public void run() {
		if ((!classFilter.isEmpty() || !featureFilter.isEmpty()) && !CollaborationModelBuilder.isFilterDefined()) {
			setChecked(true);
			CollaborationModelBuilder.setClassFilter(new HashSet<String>(classFilter));
			CollaborationModelBuilder.setFeatureFilter(new HashSet<String>(featureFilter));
			classFilter.clear();
			featureFilter.clear();
			collaborationView.refresh();
		} else {
			setChecked(false);
			classFilter.clear();
			featureFilter.clear();
			CollaborationModelBuilder.getClassFilter().clear();
			CollaborationModelBuilder.getFeatureFilter().clear();
			collaborationView.updateGuiAfterBuild(collaborationView.getFeatureProject(), null);
		}
	}
}
