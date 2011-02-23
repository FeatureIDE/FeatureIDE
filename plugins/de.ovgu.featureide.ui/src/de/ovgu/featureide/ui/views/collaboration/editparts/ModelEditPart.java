/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.ui.views.collaboration.editparts;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.FreeformLayer;
import org.eclipse.draw2d.FreeformLayout;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.MarginBorder;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.editparts.AbstractGraphicalEditPart;

import de.ovgu.featureide.ui.views.collaboration.policy.ClassXYLayoutPolicy;
import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;
import de.ovgu.featureide.ui.views.collaboration.model.Class;
import de.ovgu.featureide.ui.views.collaboration.model.Collaboration;
import de.ovgu.featureide.ui.views.collaboration.model.CollaborationModel;

/**
 * 
 * 
 * @author Constanze Adler
 */
public class ModelEditPart extends AbstractGraphicalEditPart {

	public ModelEditPart(CollaborationModel model) {
		setModel(model);
	}

	public CollaborationModel getCollaborationModel() {
		return (CollaborationModel) getModel();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.gef.editparts.AbstractGraphicalEditPart#createFigure()
	 */
	@Override
	protected IFigure createFigure() {
		Figure fig = new FreeformLayer();
		fig.setLayoutManager(new FreeformLayout());
		fig.setBorder(new MarginBorder(10));
		fig.setBackgroundColor(GUIDefaults.DIAGRAM_BACKGROUND);
		return fig;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.gef.editparts.AbstractEditPart#createEditPolicies()
	 */
	@Override
	protected void createEditPolicies() {
		installEditPolicy(EditPolicy.LAYOUT_ROLE, new ClassXYLayoutPolicy());
	}

	@Override
	protected List<?> getModelChildren() {
		CollaborationModel model = getCollaborationModel();
		List<Object> list = new LinkedList<Object>();
		addCollaboration(model.getCollaborations(), list);
		addClass(model.getClasses(), list);
		return list;
	}

	private void addCollaboration(List<Collaboration> cols, List<Object> list) {
		for (Collaboration c : cols)
			list.add(c);
	}

	private void addClass(List<Class> classes, List<Object> list) {
		for (Class c : classes)
			list.add(c);
	}

}
