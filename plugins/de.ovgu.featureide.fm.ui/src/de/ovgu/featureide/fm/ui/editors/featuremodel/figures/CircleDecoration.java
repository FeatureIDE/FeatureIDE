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
package de.ovgu.featureide.fm.ui.editors.featuremodel.figures;

import org.eclipse.draw2d.Graphics;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.swt.graphics.Color;

import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * A decoration for a feature connection that indicates the mandatory property.
 *
 * @author Thomas Thuem
 * @author Jens Meinicke
 */
public class CircleDecoration extends ConnectionDecoration implements GUIDefaults {

	public CircleDecoration(boolean fill) {
		final Color decoratorForegroundColor = FMPropertyManager.getDecoratorForegroundColor();
		setForegroundColor(decoratorForegroundColor);
		if (fill) {
			setOutline(false);
			setBackgroundColor(decoratorForegroundColor);
		} else {
			setBackgroundColor(FMPropertyManager.getDecoratorBackgroundColor());
		}
		setSize(SOURCE_ANCHOR_DIAMETER + 1, SOURCE_ANCHOR_DIAMETER + 1);
	}

	@Override
	public void setLocation(Point p) {
		super.setLocation(p.translate((-getBounds().width >> 1), (-getBounds().height >> 1)));
	}

	@Override
	protected void fillShape(Graphics graphics) {
		if (getActiveReason() != null) {
			graphics.setBackgroundColor(FMPropertyManager.getReasonColor(getActiveReason()));
		}
		final Rectangle bounds = getBounds().getShrinked(1, 1);
		Draw2dHelper.fillCircle(graphics, bounds);
	}

	@Override
	protected void outlineShape(Graphics graphics) {
		final Rectangle bounds = getBounds().getShrinked(1, 1);
		graphics.drawOval(bounds);
	}

	@Override
	public void setReferencePoint(Point p) {}
}
