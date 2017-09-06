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
//#if CallButtons
package de.ovgu.featureide.examples.elevator.core.controller;

/**
 * This interface represents the main point of interaction with the controller
 * and view. To receive any floor request you have to implement this interface.
 */
public interface ITriggerListener {
	/**
	 * This methods gets called if a trigger is fired. For example if any floor
	 * request is triggered.
	 * 
	 * @param request
	 *            The floor request that is triggered.
	 */
	void trigger(Request request);
	
}
//#endif
