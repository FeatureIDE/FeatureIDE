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
 * Event triggered by changes to a feature model or its elements.
 * 
 * @author Sebastian Krieter
 */
public class FeatureModelEvent {

	public static final String CONSTRAINT_MOVE = "CONSTRAINT_MOVE";
	public static final String CONSTRAINT_MODIFY = "CONSTRAINT_MODIFY";
	public static final String CONSTRAINT_DELETE = "CONSTRAINT_DELETE";
	public static final String CONSTRAINT_ADD = "CONSTRAINT_ADD";
	public static final String FEATURE_MODIFY = "FEATURE_MODIFY";
	public static final String FEATURE_DELETE = "FEATURE_DELETE";
	public static final String FEATURE_ADD = "FEATURE_ADD";
	public static final String STRUCTURE_CHANGED = "STRUCTURE_CHANGED";
	public static final String LEGEND_LAYOUT_CHANGED = "LEGEND_LAYOUT_CHANGED";
	public static final String MODEL_LAYOUT_CHANGED = "MODEL_LAYOUT_CHANGED";
	public static final String MODEL_DATA_CHANGED = "MODEL_DATA_CHANGED";
	public static final String MODEL_DATA_SAVED  = "MODEL_DATA_SAVED";
	public static final String MODEL_DATA_LOADED = "MODEL_DATA_LOADED";

	private final Object source;
	private final Object editor;
	private final boolean persistent;
	private final String propertyName;
	private final Object oldValue;
	private final Object newValue;

	public FeatureModelEvent(Object source, String propertyName) {
		this(source, null, false, propertyName, null, null);
	}

	public FeatureModelEvent(Object source, String propertyName, Object oldValue, Object newValue) {
		this(source, null, false, propertyName, oldValue, newValue);
	}

	public FeatureModelEvent(Object source, Object editor, boolean persistent, String propertyName, Object oldValue, Object newValue) {
		this.source = source;
		this.editor = editor;
		this.persistent = persistent;
		this.propertyName = propertyName;
		this.oldValue = oldValue;
		this.newValue = newValue;
	}

	public Object getSource() {
		return source;
	}

	public Object getEditor() {
		return editor;
	}

	public boolean isPersistent() {
		return persistent;
	}

	public String getPropertyName() {
		return propertyName;
	}

	public Object getOldValue() {
		return oldValue;
	}

	public Object getNewValue() {
		return newValue;
	}

}
