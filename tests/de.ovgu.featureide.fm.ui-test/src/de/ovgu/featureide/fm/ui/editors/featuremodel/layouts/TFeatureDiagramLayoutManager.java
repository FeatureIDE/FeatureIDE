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
package de.ovgu.featureide.fm.ui.editors.featuremodel.layouts;


import static org.junit.Assert.assertTrue;

import org.junit.Test;

import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

/**
 * Tests the checkIntersection method in FeatureDiagramLayoutManager.java
 * 
 * @author "Edgard Schmidt"
 * @author "Stefanie Schober"
 * @author "Jann-Ole Henningson"
 */


public class TFeatureDiagramLayoutManager {
	
	final static FeatureDiagramLayoutManager fdlm = new BreadthFirstLayout();
	
	@Test
	public void testCheckIntersection() {
		boolean check;
		
		//Edge is touching rectangle, but not intersecting
		Point source = new Point(0,0);
		Point target = new Point(5,0);
		Point legendPos = new Point (5,0);
		Dimension legendSize = new Dimension(10, 10);
		check = fdlm.rectangleConnectionIntersection(source, target, new Rectangle(legendPos, legendSize));
		assertTrue(check);
		
		//Edge is intersecting rectangle
		legendPos = new Point(-3,-1);
		check = fdlm.rectangleConnectionIntersection(source, target, new Rectangle(legendPos, legendSize));
		assertTrue(check);
		
		//Edge and rectangle are non-existent, i.e. too small
		source = new Point(0,0);
		target = new Point(0,0);
		legendPos = new Point(0,0);
		legendSize = new Dimension(0,0);
		check = fdlm.rectangleConnectionIntersection(source, target, new Rectangle(legendPos, legendSize));
		assertTrue(!check);
		
		legendPos = new Point(-1, -1);
		legendSize = new Dimension(2, 2);
		target = new Point(0,0);

		//Hitting rectangle from left side
		source = new Point(-2,0);
		check = fdlm.rectangleConnectionIntersection(source, target, new Rectangle(legendPos, legendSize));
		assertTrue(check);

		//Hitting rectangle from upper side
		source = new Point(0,-2);
		check = fdlm.rectangleConnectionIntersection(source, target, new Rectangle(legendPos, legendSize));
		assertTrue(check);

		//Hitting rectangle from right side
		source = new Point(2,0);
		check = fdlm.rectangleConnectionIntersection(source, target, new Rectangle(legendPos, legendSize));
		assertTrue(check);

		//Hitting rectangle from lower side
		source = new Point(0,2);
		check = fdlm.rectangleConnectionIntersection(source, target, new Rectangle(legendPos, legendSize));
		assertTrue(check);

		//Intersecting rectangle at top-left corner
		source = new Point(-4,-4);
		check = fdlm.rectangleConnectionIntersection(source, target, new Rectangle(legendPos, legendSize));
		assertTrue(check);
	}
}
