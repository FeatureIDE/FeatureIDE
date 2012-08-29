/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
package de.ovgu.featureide.fm.core;

/**
 * Provides constants for <code>PropertyChangeListener</code>.
 * 
 * @author Thomas Thuem
 * 
 */
public interface PropertyConstants {

	public final static String MODEL_DATA_LOADED = "MODEL_DATA_LOADED";
	public final static String REDRAW_DIAGRAM = "REDRAW_DIAGRAM";
	public final static String MODEL_DATA_CHANGED = "MODEL_DATA_CHANGED";
	public final static String MODEL_LAYOUT_CHANGED = "MODEL_LAYOUT_CHANGED";
	public final static String REFRESH_ACTIONS = "REFRESH_ACTIONS";
	public final static String NAME_CHANGED = "NAME_CHANGED";
	

	public final static String LOCATION_CHANGED = "LOCATION_CHANGED";// should
																		// not
																		// occur
																		// in
																		// CORE
																		// feature.

	public final static String COLOR_CHANGED = "COLOR_CHANGED";
	
	public final static String MANDATORY_CHANGED = "MANDATORY_CHANGED";
	
	public final static String HIDDEN_CHANGED = "HIDDEN_CHANGED";

	public final static String PARENT_CHANGED = "PARENT_CHANGED";

	public final static String CHILDREN_CHANGED = "CHILDREN_CHANGED";

	public final static String FEATURE_NAME_CHANGED = "NAME_CHANGED";// oldname->newname
	
	public final static String ATTRIBUTE_CHANGED = "ATTRIBUTE_CHANGED"; //changed Color Settings

	public final static String CONSTRAINT_SELECTED = "CONSTRAINT_SELECTED";
}
