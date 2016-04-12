/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.base.event;

/**
 * Provides constants for <code>IFeatureModelListener</code>.
 * 
 * @author Thomas Thuem
 */
public interface PropertyConstants {

	String REDRAW_DIAGRAM = "REDRAW_DIAGRAM";
	String REFRESH_ACTIONS = "REFRESH_ACTIONS";
	String NAME_CHANGED = "NAME_CHANGED";
	String LOCATION_CHANGED = "LOCATION_CHANGED";
	String COLOR_CHANGED = "COLOR_CHANGED";
	String MANDATORY_CHANGED = "MANDATORY_CHANGED";
	String HIDDEN_CHANGED = "HIDDEN_CHANGED";
	String PARENT_CHANGED = "PARENT_CHANGED";
	String CHILDREN_CHANGED = "CHILDREN_CHANGED";
	String FEATURE_NAME_CHANGED = "NAME_CHANGED";
	String ATTRIBUTE_CHANGED = "ATTRIBUTE_CHANGED";
	String CONSTRAINT_SELECTED = "CONSTRAINT_SELECTED";

}
