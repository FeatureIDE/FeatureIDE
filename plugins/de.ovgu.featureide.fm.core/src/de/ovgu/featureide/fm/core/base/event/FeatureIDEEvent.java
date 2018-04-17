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
package de.ovgu.featureide.fm.core.base.event;

import de.ovgu.featureide.fm.core.base.impl.FeatureModel;

/**
 * Event triggered by changes to a feature model or its elements. <br/> <br/> Each event contains the following information: <ul> <li>an event type which
 * determine the kind of event</li> <li>the sender (source) of this event, i.e., which object fired this event</li> <li>the old value (if available), and the
 * new value</li> </ul> <br/> <br/> This events are intended to be processed by {@link IEventListener} instances. <br/> <br/> For usage to fire
 * <code>FeatureIDEEvent</code>s, see {@link FeatureModel#fireEvent(FeatureIDEEvent)}.
 *
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 */
public class FeatureIDEEvent {

	/**
	 * Typing of the event instance. This type have to be used in order to distinguish of the event kind.
	 */
	public enum EventType {
		/**
		 * The constraint was moved.
		 */
		CONSTRAINT_MOVE,
		/**
		 * A constraint was modified.
		 */
		CONSTRAINT_MODIFY,
		/**
		 * A constraint was deleted.
		 */
		CONSTRAINT_DELETE,
		/**
		 * A constraint was added.
		 */
		CONSTRAINT_ADD,
		/**
		 * A constraint was selected.
		 */
		CONSTRAINT_SELECTED,
		/**
		 * A feature was modified.
		 */
		FEATURE_MODIFY,
		/**
		 * A feature was deleted.
		 */
		FEATURE_DELETE,
		/**
		 * A feature was added above another feature.
		 */
		FEATURE_ADD_ABOVE,
		/**
		 * A feature was added.
		 */
		FEATURE_ADD,
		/**
		 * A feature's name was changed.
		 */
		FEATURE_NAME_CHANGED,
		/**
		 * All features changed their name representation.
		 */
		ALL_FEATURES_CHANGED_NAME_TYPE,
		/**
		 * A color was changed.
		 */
		COLOR_CHANGED,
		/**
		 * A hidden feature was changed.
		 */
		HIDDEN_CHANGED,
		/**
		 * A collapsed feature was changed.
		 */
		COLLAPSED_CHANGED,
		/**
		 * A collapsed feature was changed.
		 */
		COLLAPSED_ALL_CHANGED,
		/**
		 * The location of an object was changed.
		 */
		LOCATION_CHANGED,
		/**
		 * A feature attributed (e.g., the "is dead" flag) changed.
		 */
		ATTRIBUTE_CHANGED,
		/**
		 * A group type changed (e.g., from "or" to "xor").
		 */
		GROUP_TYPE_CHANGED,
		/**
		 * A feature parent changed.
		 */
		PARENT_CHANGED,
		/**
		 * The mandatory state changed.
		 */
		MANDATORY_CHANGED,
		/**
		 * The feature structure changed.
		 */
		STRUCTURE_CHANGED,
		/**
		 * The legend layout was changed.
		 */
		LEGEND_LAYOUT_CHANGED,
		/**
		 * The model layout was changed (e.g., from vertical to horizontal).
		 */
		MODEL_LAYOUT_CHANGED,
		/**
		 * The model data changed (i.e., the underlying model file was changed).
		 */
		MODEL_DATA_CHANGED,
		/**
		 * The model data was saved to file.
		 */
		MODEL_DATA_SAVED,
		/**
		 * The model data was loaded from file.
		 */
		MODEL_DATA_LOADED,
		/**
		 * The model data loaded from a file has overridden the internal model instance.
		 */
		MODEL_DATA_OVERRIDDEN,
		/**
		 * The diagram was redrawn.
		 */
		REDRAW_DIAGRAM,
		/**
		 * The refresh action command was triggered.
		 */
		REFRESH_ACTIONS,
		/**
		 * The children of a feature changed.
		 */
		CHILDREN_CHANGED,
		/**
		 * The dependency for a subtree was calculated.
		 */
		DEPENDENCY_CALCULATED,
		/**
		 * The active explanation changed.
		 */
		ACTIVE_EXPLANATION_CHANGED,
		/**
		 * Any feature attribute was added or altered.
		 */
		FEATURE_ATTRIBUTE_CHANGED,
		/**
		 * The active reason changed. Events of this type are fired for feature model elements when the active explanation has changed. It would be possible to
		 * instead simply notify each affected feature model element of the new active explanation. However, this would lead to a negative performance impact as
		 * each feature model would have to search the explanation for the relevant reason again. As such, each event of this type carries the respective reason
		 * so the feature model element does not have to look for it itself.
		 */
		ACTIVE_REASON_CHANGED,
		/**
		 * Default. Do nothing.
		 */
		DEFAULT,
	}

	static FeatureIDEEvent[] defaultEvents = new FeatureIDEEvent[EventType.values().length];
	static {
		for (final EventType e : EventType.values()) {
			defaultEvents[e.ordinal()] = new FeatureIDEEvent(e);
		}
	}

	public static FeatureIDEEvent getDefault(final EventType e) {
		return defaultEvents[e.ordinal()];
	}

	private final Object source;
	private final EventType eventType;
	private final Object oldValue;
	private final Object newValue;

	private FeatureIDEEvent(EventType e) {
		this(null, e);
	}

	public FeatureIDEEvent(Object source, EventType eventType) {
		this(source, eventType, null, null);
	}

	public FeatureIDEEvent(Object source, EventType eventType, Object oldValue, Object newValue) {
		this.source = source;
		this.eventType = eventType;
		this.oldValue = oldValue;
		this.newValue = newValue;
	}

	public Object getSource() {
		return source;
	}

	public EventType getEventType() {
		return eventType;
	}

	public Object getOldValue() {
		return oldValue;
	}

	public Object getNewValue() {
		return newValue;
	}

	@Override
	public String toString() {
		return "FeatureIDEEvent [source=" + source + ", eventType=" + eventType + ", oldValue=" + oldValue + ", newValue=" + newValue + "]";
	}

}
