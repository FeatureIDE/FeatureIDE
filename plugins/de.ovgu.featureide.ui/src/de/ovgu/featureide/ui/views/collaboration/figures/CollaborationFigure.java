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
import org.eclipse.draw2d.GridLayout;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import de.ovgu.featureide.core.fstmodel.FSTConfiguration;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;

/**
 * An instance of this class represents the graphical representation of the Collaboration.
 *
 * @author Constanze Adler
 */
public class CollaborationFigure extends Figure implements GUIDefaults {

	private final Label label = new Label();
	public boolean selected = true;
	public boolean isConfiguration = false;

	public CollaborationFigure(FSTFeature coll) {
		super();

		selected = coll.isSelected();
		isConfiguration = coll instanceof FSTConfiguration;
		final GridLayout gridLayout = new GridLayout(1, true);
		gridLayout.verticalSpacing = GRIDLAYOUT_VERTICAL_SPACING;
		gridLayout.marginHeight = GRIDLAYOUT_MARGIN_HEIGHT - 1;
		setLayoutManager(gridLayout);

		setBackgroundColor(ROLE_BACKGROUND);

		if (selected) {
			setBorder(COLL_BORDER_SELECTED);
		} else {
			setBorder(COLL_BORDER_UNSELECTED);
		}
		if (isConfiguration) {
			if (((FSTConfiguration) coll).isSelected()) {
				label.setIcon(IMAGE_CURRENT_CONFIGURATION);
			} else {
				label.setIcon(IMAGE_CONFIGURATION);
			}
		}
		label.setFont(DEFAULT_FONT);
		label.setLocation(new Point(COLLABORATION_INSETS.left, COLLABORATION_INSETS.top));

		setName(coll.getName());
		this.add(label);

		setOpaque(true);
	}

	private void setName(String name) {
		label.setText(name);
		final Dimension labelSize = label.getPreferredSize();

		if (labelSize.equals(label.getSize())) {
			return;
		}
		label.setSize(labelSize);

		final Rectangle bounds = getBounds();
		final int w = COLLABORATION_INSETS.getWidth();
		final int h = COLLABORATION_INSETS.getHeight();
		bounds.setSize(labelSize.expand(w, h));
		final Dimension oldSize = getSize();

		if (!oldSize.equals(0, 0)) {
			final int dx = (oldSize.width - bounds.width) / 2;
			bounds.x += dx;
		}
		setBounds(bounds);
	}

	@Override
	public String toString() {
		return label.getText();
	}
}
