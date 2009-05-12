/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package featureide.fm.ui.editors.featuremodel.figures;

import org.eclipse.draw2d.Ellipse;
import org.eclipse.draw2d.Graphics;
import org.eclipse.draw2d.RotatableDecoration;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import featureide.fm.core.Feature;
import featureide.fm.ui.editors.FeatureUIHelper;
import featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * A decoration for a feature connection that indicates its group type.
 * 
 * @author Thomas Thuem
 */
public class RelationDecoration extends Ellipse implements RotatableDecoration, GUIDefaults {
	
	private boolean fill;
	
	private Point referencePoint;

	private Feature lastChild;

	public RelationDecoration(boolean fill, Feature lastChild) {
		super();
		this.fill = fill;
		this.lastChild = lastChild;
		setForegroundColor(DECORATOR_FOREGROUND);
		setBackgroundColor(DECORATOR_FOREGROUND);
		setSize(TARGET_ANCHOR_DIAMETER, TARGET_ANCHOR_DIAMETER/2);
	}
	
	@Override
	public void setLocation(Point p) {
		super.setLocation(p.translate(-TARGET_ANCHOR_DIAMETER/2, 0));
	}
	
	public void setReferencePoint(Point p) {
		referencePoint = p;
	}
	
	@Override
	protected void fillShape(Graphics graphics) {
		if (!fill)
			return;
		
		Rectangle r = calculateRectangle();

		int angle1 = HALF_ARC ? 180 : calculateAngle(r.getCenter(), referencePoint);
		int angle2 = HALF_ARC ? 360 : calculateAngle(r.getCenter(), FeatureUIHelper.getSourceLocation(lastChild));

		if (angle1 + 1 < angle2)
			graphics.fillArc(r, angle1, angle2 - angle1);
	}
	
	@Override
	protected void outlineShape(Graphics graphics) {
		if (fill)
			return;
		
		Rectangle r = calculateRectangle();
		r.shrink(lineWidth, lineWidth);

		int angle1 = HALF_ARC ? 180 : calculateAngle(r.getCenter(), referencePoint);
		int angle2 = HALF_ARC ? 360 : calculateAngle(r.getCenter(), FeatureUIHelper.getSourceLocation(lastChild));

		if (angle1 + 1 < angle2)
			graphics.drawArc(r, angle1, angle2 - angle1);
	}
	
	private Rectangle calculateRectangle() {
		Rectangle r = Rectangle.SINGLETON;
		r.setBounds(getBounds());
		r.y -= TARGET_ANCHOR_DIAMETER/2;
		r.height = TARGET_ANCHOR_DIAMETER;
		r.shrink(lineWidth + 1, lineWidth + 1);
		return r;
	}

	private int calculateAngle(Point point, Point referencePoint) {
		int dx = referencePoint.x - point.x;
		int dy = referencePoint.y - point.y;
		return 360 - (int) Math.round(Math.atan2(dy, dx)/Math.PI*180);
	}

}
