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
package de.ovgu.featureide.fm.ui.utils;

import org.eclipse.draw2d.PositionConstants;
import org.eclipse.draw2d.Viewport;
import org.eclipse.draw2d.geometry.Insets;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.GraphicalEditPart;
import org.eclipse.gef.editparts.ViewportAutoexposeHelper;

/**
 * Autoexposer which allows the pointer to be outside of the viewport
 * 
 * Refactered version of VIewportAutoexposeHelper. Does not implement AutoexposeHelper by itself because ViewportHelper is not visible.
 */
public class FullViewportAutoexposeHelper extends ViewportAutoexposeHelper {

	/**
	 * Simple stop watch
	 * 
	 * TODO: Is there any equivalent class in the APIs?
	 */
	private class Timer {

		private long lastTime = 0;

		/**
		 * Deactivates the timer
		 */
		public void reset() {
			lastTime = 0;
		}

		/**
		 * Returns the number of milliseconds since the last invocation
		 * 
		 * If the timer have not been started yet, start the timer and return 0
		 * 
		 * @return milliseconds since last call, or 0 if the timer was not active
		 */
		public long get() {
			final long current = System.currentTimeMillis();
			if (0 == lastTime) {
				lastTime = current;
				return 0;
			}
			final long difference = current - lastTime;
			lastTime = current;
			return difference;
		}
	}

	private Insets insets;
	private Timer timer = new Timer();
	final private float speed;

	public FullViewportAutoexposeHelper(GraphicalEditPart owner, Insets finsets, float fspeed) {
		super(owner, finsets);
		insets = finsets;
		speed = fspeed;
	}

	@Override
	public boolean detect(Point point) {
		timer.reset();
		return shouldScroll(point);
	}

	@Override
	public boolean step(Point point) {
		if (!shouldScroll(point)) {
			return false;
		}

		Viewport port = findViewport(owner);
		Point oldLoc = port.getViewLocation();
		Point newLoc = getNewLocation(oldLoc, getInnerBounds().getPosition(point), getOffset());
		port.setViewLocation(newLoc);
		return true;
	}

	/**
	 * check if the pointer is in an area which is sensitive to DND
	 * @param point
	 * @return true when the pointer is in such an area
	 */
	private boolean shouldScroll(Point point) {
		return !getInnerBounds().contains(point);
	}

	/**
	 * Returns the bounds of the area which is not sensitive to DND
	 * 
	 * @return the bounds
	 */
	private Rectangle getInnerBounds() {
		Viewport port = findViewport(owner);

		Rectangle rect = Rectangle.SINGLETON.getCopy();
		port.getClientArea(rect);
		port.translateToParent(rect);
		port.translateToAbsolute(rect);
		rect.crop(insets);

		return rect;
	}

	/**
	 * Calculates a new viewport position
	 * 
	 * @param old old position
	 * @param direction @see org.eclipse.draw2d.PositionConstants
	 * @param scrollOffset absolute offset value
	 * @return
	 */
	private Point getNewLocation(Point old, int direction, int scrollOffset) {
		Point loc = old.getCopy();
		if ((direction & PositionConstants.SOUTH) != 0) loc.y += scrollOffset;
		else if ((direction & PositionConstants.NORTH) != 0) loc.y -= scrollOffset;

		if ((direction & PositionConstants.EAST) != 0) loc.x += scrollOffset;
		else if ((direction & PositionConstants.WEST) != 0) loc.x -= scrollOffset;

		return loc;
	}

	/**
	 * Calculate the offset incorporating the speed factor and the time
	 * 
	 * @return offset
	 */
	private int getOffset() {
		return (int) (timer.get() * speed);
	}

}
