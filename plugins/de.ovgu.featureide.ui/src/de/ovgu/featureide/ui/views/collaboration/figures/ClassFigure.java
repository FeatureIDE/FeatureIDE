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
import org.eclipse.draw2d.FreeformLayout;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;
import de.ovgu.featureide.ui.views.collaboration.model.Class;

/**
 * An instance of this class represents the graphical representation of the 
 * Class with in the Collaboration Diagram.
 * 
 * @author Constanze Adler
 */
public class ClassFigure extends Figure implements GUIDefaults{
	
	private final Label label = new Label();
	private static int DEFAULT_WIDTH = 100;
	private int height;

	
	public ClassFigure(Class c, int height) {
		
		super();
		
		this.setLayoutManager(new FreeformLayout());

		if (c.isOpenEditor) {
			setBackgroundColor(OPEN_CLASS_BACKGROUND);
			setBorder(CLASS_BORDER_SELECTED);
		} else {
			setBackgroundColor(CLASS_BACKGROUND);
			setBorder(CLASS_BORDER);
			
		}
		
		label.setForegroundColor(FOREGROUND);
		label.setFont(DEFAULT_FONT);
		label.setLocation(new Point(CLASS_INSETS.left, CLASS_INSETS.top));
		this.height = height;
		this.setName(c.getName());
	
		this.add(label);
		this.setOpaque(false);
			
	}
	
	private void setName(String name){
		label.setText(name);
		Dimension labelSize = label.getPreferredSize();
		
		if (labelSize.width < DEFAULT_WIDTH)
			labelSize.width = DEFAULT_WIDTH;
		
		if (labelSize.equals(label.getSize()))
			return;
		
		label.setSize(labelSize);

		Rectangle bounds = getBounds();
		int w = CLASS_INSETS.getWidth();
		
		bounds.setSize(labelSize.expand(w, height));

		Dimension oldSize = getSize();
		if (!oldSize.equals(0, 0)) {
			int dx = (oldSize.width - bounds.width) / 2;
			bounds.x += dx;
		}
		setBounds(bounds);
	}
}
