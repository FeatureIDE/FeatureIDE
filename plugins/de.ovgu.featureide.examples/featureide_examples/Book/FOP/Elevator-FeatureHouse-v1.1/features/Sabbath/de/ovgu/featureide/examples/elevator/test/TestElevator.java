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
package de.ovgu.featureide.examples.elevator.test;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.Queue;

/**
 * 
 * This class implements tests for the simulation.
 * 
 * @author FeatureIDE Team
 */
public class TestElevator {

	private Queue<String> expectedResult =
		new LinkedList<String>(Arrays.asList(
				"1 MOVING_UP",
				"1 FLOORING",
				"2 MOVING_UP",
				"2 FLOORING",
				"3 MOVING_UP",
				"3 FLOORING",
				"2 MOVING_DOWN",
				"2 FLOORING",
				"1 MOVING_DOWN",
				"1 FLOORING",
				"0 MOVING_DOWN",
				"0 FLOORING",
				"1 MOVING_UP",
				"1 FLOORING"));

}
