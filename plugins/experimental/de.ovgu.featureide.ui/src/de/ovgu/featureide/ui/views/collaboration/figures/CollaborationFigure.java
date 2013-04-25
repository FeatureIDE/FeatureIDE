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
package de.ovgu.featureide.ui.views.collaboration.figures;

import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.GridLayout;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;
import de.ovgu.featureide.ui.views.collaboration.model.Collaboration;

/**
 * An instance of this class represents the graphical representation of the 
 * Collaboration.
 * 
 * @author Constanze Adler
 */
public class CollaborationFigure extends Figure implements GUIDefaults{

	private final Label label = new Label();
	public boolean selected = true;
	public boolean isConfiguration = false;
	
	public CollaborationFigure(Collaboration coll) {
		super();
		selected = coll.selected;
		isConfiguration = coll.isConfiguration;
		GridLayout gridLayout = new GridLayout(1, true);
		gridLayout.verticalSpacing = GRIDLAYOUT_VERTICAL_SPACING;
		gridLayout.marginHeight = GRIDLAYOUT_MARGIN_HEIGHT - 1;
		this.setLayoutManager(gridLayout);

		this.setBackgroundColor(ROLE_BACKGROUND);
		
		if (selected) {
			this.setBorder(COLL_BORDER_SELECTED);
		} else {
			this.setBorder(COLL_BORDER_UNSELECTED);
		}
		if (isConfiguration)
			if (selected)
				label.setIcon(IMAGE_CURRENT_CONFIGURATION);
			else
				label.setIcon(IMAGE_CONFIGURATION);
		
		label.setFont(DEFAULT_FONT);
		label.setLocation(new Point(COLLABORATION_INSETS.left, COLLABORATION_INSETS.top));
		
		this.setName(coll.getName());
		this.add(label);
		
		this.setOpaque(true);
	}

	private void setName(String name){
		label.setText(name);
		Dimension labelSize = label.getPreferredSize();
		
		if (labelSize.equals(label.getSize()))
			return;
		label.setSize(labelSize);

		Rectangle bounds = getBounds();
		int w = COLLABORATION_INSETS.getWidth();
		int h = COLLABORATION_INSETS.getHeight();
		bounds.setSize(labelSize.expand(w, h));
		Dimension oldSize = getSize();
		
		if (!oldSize.equals(0, 0)) {
			int dx = (oldSize.width - bounds.width) / 2;
			bounds.x += dx;
		}
		setBounds(bounds);
	}
}
