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
package de.ovgu.featureide.ui.views.collaboration.figures;

import org.eclipse.draw2d.Figure;

import de.ovgu.featureide.ui.editors.annotation.ColorPalette;
import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;
import de.ovgu.featureide.ui.views.collaboration.model.Collaboration;


/**
 * 
 * @author Sebastian Krieter
 * @author Steffen Schulze
 */
public class UnderlayerFigure extends Figure implements GUIDefaults{

	private CollaborationFigure collaborationFigure;
	
	public UnderlayerFigure(Collaboration coll) {
		super();
		collaborationFigure = new CollaborationFigure(coll);
		this.add(collaborationFigure);
		
		collaborationFigure.setLocation(COLLFIGURE_LOCATION);
		this.setSize(0, DEFAULT_UNDERLAYER_HEIGHT);

		if (coll.hasFeature() && coll.hasFeatureColor()) {
			this.setBackgroundColor(ColorPalette.getColor(coll.getFeatureColor(), 0.4f));
		}
		
		this.setOpaque(true);
	}
	
	public void setCollaborationFigureWidth(int width) {
		collaborationFigure.getBounds().width=width;
	}

	public int getCollaborationFigureWidth() {
		return collaborationFigure.getBounds().width;
	}	
	
	/**
	 * @return the collaborationFigure
	 */
	public CollaborationFigure getCollaborationFigure() {
		return collaborationFigure;
	}
}
