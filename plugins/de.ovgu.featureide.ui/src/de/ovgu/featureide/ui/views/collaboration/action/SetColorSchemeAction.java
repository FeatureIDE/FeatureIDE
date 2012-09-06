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
package de.ovgu.featureide.ui.views.collaboration.action;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.ui.views.collaboration.CollaborationView;

/**
 * Action to select a colorscheme
 * 
 * @author Sebastian Krieter
 */
public class SetColorSchemeAction extends AbstractColorAction {
	
	public SetColorSchemeAction(String text, GraphicalViewerImpl view, CollaborationView collaborationView, int index) {
		super(text, view, collaborationView, index, Action.AS_CHECK_BOX);
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.views.collaboration.color.action.AbstractColorAction#action(de.ovgu.featureide.fm.core.Feature)
	 */
	@Override
	protected boolean action(FeatureModel fm, String collName) {
		if (fm.getColorschemeTable().getSelectedColorscheme() != index) {
			fm.getColorschemeTable().setSelectedColorscheme(index);
		} else {
			fm.getColorschemeTable().setEmptyColorscheme();
		}
		return true;
	}
	
}
