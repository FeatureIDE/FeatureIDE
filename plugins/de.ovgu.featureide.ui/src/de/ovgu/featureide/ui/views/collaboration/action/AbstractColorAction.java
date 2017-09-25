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

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.IStructuredSelection;

import de.ovgu.featureide.core.fstmodel.FSTConfiguration;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.ui.views.collaboration.CollaborationView;
import de.ovgu.featureide.ui.views.collaboration.editparts.CollaborationEditPart;

/**
 * The superclass for all actions in the color contextmenu
 *
 * @author Sebastian Krieter
 */
public abstract class AbstractColorAction extends Action {

	private GraphicalViewerImpl viewer;
	protected CollaborationView collaborationView;
	protected int index;

	public AbstractColorAction(String text) {
		setText(text);
	}

	public AbstractColorAction(String text, GraphicalViewerImpl view, CollaborationView collaborationView, int index) {
		super(text);
		viewer = view;
		this.index = index;
		this.collaborationView = collaborationView;
	}

	public AbstractColorAction(String text, GraphicalViewerImpl view, CollaborationView collaborationView, int index, int style) {
		super(text, style);
		viewer = view;
		this.index = index;
		this.collaborationView = collaborationView;
	}

	@Override
	public void run() {
		final Object selectedItem = ((IStructuredSelection) viewer.getSelection()).getFirstElement();

		if (selectedItem instanceof CollaborationEditPart) {
			final FSTFeature coll = ((CollaborationEditPart) selectedItem).getCollaborationModel();
			if (!(coll instanceof FSTConfiguration)) {
				final IFeatureModel fm = collaborationView.getFeatureProject().getFeatureModel();

				final boolean refresh = action(fm, coll.getName());

				if (refresh) {
					collaborationView.refreshAll();
				}
			}
		}
	}

	protected abstract boolean action(IFeatureModel fm, String collName);
}
