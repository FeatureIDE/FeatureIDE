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
package de.ovgu.featureide.fm.core.base;

import java.util.Collection;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.Set;

/**
 * Classes implementing <code>IPropertyContainer</code> act as objects that can be enriched with arbitrary user-defined values by key-value mappings
 * ("properties").
 *
 * @author Marcus Pinencke
 * @since 3.0
 */
public interface IPropertyContainer {

	/**
	 * Thrown by <code>IPropertyContainer</code> implementations indicating a request for a unknown property, e.g., by reading from an unknown <code>key</code>
	 *
	 * @author Marcus Pinencke
	 * @since 3.0
	 */
	class NoSuchPropertyException extends NoSuchElementException {

		private static final long serialVersionUID = 6923332230285211910L;

		public NoSuchPropertyException(String key) {
			super("The container does not contain a property with the given key:" + key);
		}
	}

	public static class Entry {

		private final String key;
		private final String type;

		private String value;

		public Entry(Entry oldEntry) {
			key = oldEntry.key;
			type = oldEntry.type;
			value = oldEntry.value;
		}

		public Entry(String key, String type, String value) {
			this.key = key == null ? null : key.toLowerCase();
			this.type = type == null ? null : type.toLowerCase();
			this.value = value;
		}

		public Entry(String key, String type) {
			this(key, type, null);
		}

		@Override
		public int hashCode() {
			return Objects.hash(key, type);
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj) {
				return true;
			}
			if ((obj == null) || (getClass() != obj.getClass())) {
				return false;
			}
			final Entry other = (Entry) obj;
			return Objects.equals(key, other.key) && Objects.equals(type, other.type);
		}

		public String getKey() {
			return key;
		}

		public String getType() {
			return type;
		}

		public String getValue() {
			return value;
		}

		public void setValue(String value) {
			this.value = value;
		}

		@Override
		public String toString() {
			return "Entry [key=" + key + ", type=" + type + ", value=" + value + "]";
		}
	}

	/**
	 * Reads a per-object user-defined property identified by a custom <code>key</code>, and returns the stored value if a value was assigned by calling
	 * {@link IPropertyContainer#set(String, Type, Object)} earlier. Properties are stored persistently if ValueProtection.NORMAL_PROTECTION or
	 * ValueProtection.READ_ONLY_PERSISTENT was used when calling {@link IPropertyContainer#set(String, Type, Object)} or temporarily. The latest (maybe
	 * volatile) state will be taken into account, depending on the call of {@link IPropertyContainer#remove(String)}. If no value was assigned (the <code>key
	 * is unknown</code>), the <code>defaultValue</code> will be returned.
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 *
	 * @see IPropertyContainer#get(String, String)
	 * @see IPropertyContainer#has(String, String)
	 * @see IPropertyContainer#remove(String, String)
	 *
	 * @param key property name (case insensitive)
	 * @param type type name (case insensitive)
	 * @param defaultValue value to return if no property is set
	 * @return value associated with <code>key</code> if set, <code>defaultValue</code> otherwise
	 */
	String get(String key, String type, String defaultValue);

	/**
	 * Reads a per-object user-defined property identified by a custom <code>key</code>, and returns the stored value if a value was assigned by calling
	 * {@link IPropertyContainer#set(String, String, String)} earlier. Properties are stored persistently such that an assignment will be alive as long as it
	 * was not removed by calling {@link IPropertyContainer#remove(String, String)}. If no value was assigned (the <code>key is unknown</code>), a
	 * <code>NoSuchPropertyException</code> will be thrown.
	 *
	 * @see IPropertyContainer#get(String, Object)
	 * @see IPropertyContainer#has(String)
	 * @see IPropertyContainer#remove(String)
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 *
	 * @param key property name (case insensitive)
	 * @param type type name (case insensitive)
	 * @return value associated with <code>key</code> if set. If <code>key</code> is not known, throws <code>NoSuchPropertyException</code>.
	 */
	String get(String key, String type) throws NoSuchPropertyException;

	/**
	 * Checks if this object contains a property associated with the given <code>key</code>. Returns <code>true</code> if at some point earlier
	 * {@link IPropertyContainer#set(String, String, String)} was called with the corresponding <code>key</code>. Properties are stored persistently such that
	 * an assignment will be alive as long as it was not removed by calling {@link IPropertyContainer#remove(String, String)}, and, hence, <code>key</code> will
	 * be alive. If no property is associated to <code>key</code> the method will return <code>false</code>.
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 *
	 * @param key property name (case insensitive)
	 * @param type type name (case insensitive)
	 * @return <b>true</b> if the object contains a property associated to <code>key</code>, <b>false</b> otherwise.
	 */
	boolean has(final String key, String type);

	/**
	 * Returns a distinct collection of each assigned key for this object in (possible empty) set. Since keys are case-insensitive it depends on the
	 * implementation if the user-defined strings once passed as keys are changed in some way, e.g., by converting to lower case strings.
	 *
	 * @return all properties stored in this object
	 */
	Set<Entry> getProperties();

	Set<Entry> getProperties(String type);

	/**
	 * Removes the content of this container and stores the entries <code>entries</code> into this one. The entries are copied, such that <code>entries !=
	 * this.getPropertyEntries()</code> afterwards, which also holds for any entry inside <code>entries</code>.
	 *
	 * @param entries Entries to import
	 */
	void setProperties(final Collection<Entry> entries);

	/**
	 * Removes a per-object user-defined property identified by a custom <code>key</code> and value assigned by calling
	 * {@link IPropertyContainer#set(String, String, String)} earlier. Properties are stored persistently such that an assignment will be alive as long as it
	 * this method does not remove the property. If this object does not contain any property associated to <code>key</code>, a
	 * <code>NoSuchPropertyException</code>
	 * will be thrown.
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 *
	 * @see IPropertyContainer#has(String)
	 * @see IPropertyContainer#set(String, Type, Object)
	 *
	 * @param key property name (case insensitive)
	 * @param type type name (case insensitive)
	 */
	Entry remove(final String key, String type);

	/**
	 * Sets a per-object user-defined property consisting of a <code>values</code> associated with a user-defined <code>key</code>. If <code>key</code> is
	 * already set, the behavior of this method depends on the <code>KeyConflictPolicy</code>. <br> <br> Properties are stored persistently such that an
	 * assignment will be alive as long as it was not removed by calling {@link IPropertyContainer#remove(String, String)}. <br> <br> To receive the value
	 * behind a <code>key</code>, call {@link IPropertyContainer#get(String, String)}.
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 *
	 * @param key property name (case insensitive)
	 * @param type type name (case insensitive)
	 * @param value value to be stored
	 */
	void set(final String key, final String type, final String value);

}
