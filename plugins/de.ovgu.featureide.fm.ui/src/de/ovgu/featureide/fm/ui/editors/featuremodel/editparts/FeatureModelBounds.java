/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors.featuremodel.editparts;

import java.util.List;

import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalElement;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.CollapsedDecoration;

/**
 * Calculates the Bounds of the IGraphicalFeatureModel
 *
 * @author Insansa Michel
 * @author Malek Badeer
 */
public class FeatureModelBounds {

	public Rectangle getFeatureModelBounds(List<? extends IGraphicalElement> elements) {
		final Point min = new Point(Integer.MAX_VALUE, Integer.MAX_VALUE);
		final Point max = new Point(Integer.MIN_VALUE, Integer.MIN_VALUE);
		boolean mostRightFeature = false;

		/*
		 * update lowest, highest, most left, most right coordinates for elements
		 */

		for (final IGraphicalElement element : elements) {

			Rectangle position = FeatureUIHelper.getBounds(element);
			if (position.x < min.x) {
				min.x = position.x;
			}
			if (position.y < min.y) {
				min.y = position.y;
			}
			if ((position.right()) > max.x) {
				mostRightFeature = true;
				max.x = position.right();
			}
			if ((position.bottom()) > max.y) {
				max.y = position.bottom();
			}

			if (element instanceof IGraphicalFeature) {
				if (((IGraphicalFeature) element).isCollapsed()) {
					if (((IGraphicalFeature) element).getCollapsedDecoration() != null) {
						final CollapsedDecoration collapsedDecoration = ((IGraphicalFeature) element).getCollapsedDecoration();
						position = getBounds(collapsedDecoration);
						if (!((position.x == 0) && (position.y == 0))) {
							if (position.x < min.x) {
								min.x = position.x;
							}
							if (position.y < min.y) {
								min.y = position.y;
							}
							if ((position.right()) > max.x) {
								max.x = position.right();
							}
							if ((position.bottom()) > max.y) {
								max.y = position.bottom();
							}
						} else if (mostRightFeature) {
							if (element.getGraphicalModel().getLayout().hasVerticalLayout()) {
								max.x = max.x + position.width;
							}
						}
					}
				}
			}
			mostRightFeature = false;
		}
		return new Rectangle(min, max);
	}

	public Rectangle getBounds(CollapsedDecoration element) {
		return new Rectangle(element.getLocation(), element.getSize());
	}

}
