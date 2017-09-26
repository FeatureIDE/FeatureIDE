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
package de.ovgu.featureide.ui.views.collaboration.figures;

import org.eclipse.draw2d.Figure;

import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.fm.core.color.ColorPalette;
import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;

/**
 * A graphical element which holds a {@link CollaborationFigure}.
 *
 * @author Sebastian Krieter
 * @author Steffen Schulze
 */
public class UnderlayerFigure extends Figure implements GUIDefaults {

	private final CollaborationFigure collaborationFigure;

	public UnderlayerFigure(FSTFeature coll) {
		super();
		collaborationFigure = new CollaborationFigure(coll);
		this.add(collaborationFigure);

		collaborationFigure.setLocation(COLLFIGURE_LOCATION);
		this.setSize(0, DEFAULT_UNDERLAYER_HEIGHT);

		if (coll.getColor() != -1) {
			setBackgroundColor(ColorPalette.getColor(coll.getColor(), 0.4f));
		}

		setOpaque(true);
	}

	public void setCollaborationFigureWidth(int width) {
		collaborationFigure.getBounds().width = width;
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

	@Override
	public String toString() {
		return collaborationFigure.toString();
	}
}
