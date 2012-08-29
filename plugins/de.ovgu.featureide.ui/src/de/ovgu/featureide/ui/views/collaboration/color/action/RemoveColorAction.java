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
package de.ovgu.featureide.ui.views.collaboration.color.action;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.ui.views.collaboration.CollaborationView;

/**
 * TODO description
 * 
 * @author Sebastian Krieter
 */
public class RemoveColorAction extends AbstractColorAction {
	
	public RemoveColorAction(String text, GraphicalViewerImpl view,
			CollaborationView collaborationView) {
		super(text, view, collaborationView, 0);
		setImageDescriptor(PlatformUI.getWorkbench().getSharedImages()
				.getImageDescriptor(ISharedImages.IMG_ETOOL_DELETE));
	}

	@Override
	protected boolean action(FeatureModel fm, String collName) {
		Feature feat = fm.getFeature(collName);
		if (feat != null && feat.hasColor()) {
			feat.removeColor();
			return true;
		}
		return false;
	}
}
