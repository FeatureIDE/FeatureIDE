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
package de.ovgu.featureide.fm.core.base;

import java.util.NoSuchElementException;
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

	public static class Entry<K, T, V> {

		@Override
		public String toString() {
			return "Entry [key=" + key + ", type=" + type + ", value=" + value + "]";
		}

		K key;
		T type;
		V value;

		public Entry(K key, T type, V value) {
			this.key = key;
			this.type = type;
			this.value = value;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = (prime * result) + ((key == null) ? 0 : key.hashCode());
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			@SuppressWarnings("unchecked")
			final Entry<K, T, V> other = (Entry<K, T, V>) obj;
			if (key == null) {
				if (other.key != null) {
					return false;
				}
			} else if (!key.equals(other.key)) {
				return false;
			}
			return true;
		}

		public K getKey() {
			return key;
		}

		public T getType() {
			return type;
		}

		public V getValue() {
			return value;
		}
	}

	enum Type {
		BYTE, SHORT, INT, LONG, FLOAT, DOUBLE, BOOLEAN, CHAR, STRING
	}

	/**
	 * Reads a per-object user-defined property identified by a custom <code>key</code>, and returns the stored value if a value was assigned by calling
	 * {@link IPropertyContainer#set(String, Class, Object)} earlier. Properties are stored persistently if {@link ValueProtection#NORMAL_PERSISTENT} or
	 * {@link ValueProtection#READ_ONLY_PERSISTENT} was used when calling
	 * {@link IPropertyContainer#setProperty(String, Class, Object, KeyConflictPolicy, ValueProtection)} or temporarily. The latest (maybe volatile) state will
	 * be taken into account, depending on the call of {@link IPropertyContainer#remove(String)}. If no value was assigned (the <code>key is unknown</code>),
	 * the <code>defaultValue</code> will be returned.
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 *
	 * @see IPropertyContainer#get(String, Class)
	 * @see IPropertyContainer#has(String)
	 * @see IPropertyContainer#remove(String)
	 *
	 * @param key property name (case insensitive)
	 * @param defaultValue value to return if no property is set
	 * @return value associated with <code>key</code> if set, <code>defaultValue</code> otherwise
	 */
	<T> T get(final String key, final T defaultValue);

	Type getDataType(final String key) throws NoSuchPropertyException;

	/**
	 * Reads a per-object user-defined property identified by a custom <code>key</code>, and returns the stored value if a value was assigned by calling
	 * {@link IPropertyContainer#set(String, Class, Object)} earlier. Properties are stored persistently such that an assignment will be alive as long as it was
	 * not removed by calling {@link IPropertyContainer#remove(String)}. If no value was assigned (the <code>key is unknown</code>), a
	 * <code>NoSuchPropertyException</code> will be thrown.
	 *
	 * @see IPropertyContainer#getProperty(String, Class, Object)
	 * @see IPropertyContainer#has(String)
	 * @see IPropertyContainer#remove(String)
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 *
	 * @param key property name (case insensitive)
	 * @param type type of returning value
	 * @param defaultValue value to return if no property is set
	 * @return value associated with <code>key</code> if set. If <code>key</code> is not known, throws <code>NoSuchPropertyException</code>.
	 */
	<T> T get(final String key) throws NoSuchPropertyException;

	/**
	 * Checks if this object contains a property associated with the given <code>key</code>. Returns <code>true</code> if at some point earlier
	 * {@link IPropertyContainer#set(String, Class, Object)} was called with the corresponding <code>key</code>. Properties are stored persistently such that an
	 * assignment will be alive as long as it was not removed by calling {@link IPropertyContainer#remove(String)}, and, hence, <code>key</code> will be alive.
	 * If no property is associated to <code>key</code> the method will return <code>false</code>.
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 *
	 * @param key property name (case insensitive)
	 * @return <b>true</b> if the object contains a property associated to <code>key</code>, <b>false</b> otherwise.
	 */
	boolean has(final String key);

	/**
	 * Returns a distinct collection of each assigned key for this object in (possible empty) set. Since keys are case-insensitive it depends on the
	 * implementation if the user-defined strings once passed as keys are changed in some way, e.g., by converting to lower case strings.
	 *
	 * @return all keys of properties assigned to this object
	 */
	Set<String> keySet();

	Set<Entry<String, Type, Object>> entrySet();

	/**
	 * Removes the content of this container and stores the entries <code>entries</code> into this one. The entries are copied, such that <code>entries !=
	 * this.getPropertyEntries()</code> afterwards, which also holds for any entry inside <code>entries</code>.
	 *
	 * @param entries Entries to import
	 */
	void setEntrySet(final Set<Entry<String, Type, Object>> entries);

	/**
	 * Removes a per-object user-defined property identified by a custom <code>key</code> and value assigned by calling
	 * {@link IPropertyContainer#set(String, Class, Object)} earlier. Properties are stored persistently such that an assignment will be alive as long as it
	 * this method does not remove the property. If this object does not contain any property associated to <code>key</code>, a
	 * <code>NoSuchPropertyException</code> will be thrown.
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 *
	 * @see IPropertyContainer#has(String)
	 * @see IPropertyContainer#setProperty(String)
	 *
	 * @param key property name (case insensitive)
	 * @throws NoSuchPropertyException
	 */
	void remove(final String key) throws NoSuchPropertyException;

	/**
	 * Sets a per-object user-defined property consisting of a <code>values</code> associated with a user-defined <code>key</code>. If <code>key</code> is
	 * already set, the behavior of this method depends on the <code>KeyConflictPolicy</code>. <br/> <br/> Properties are stored persistently such that an
	 * assignment will be alive as long as it was not removed by calling {@link IPropertyContainer#remove(String)}. <br/> <br/> To receive the value behind a
	 * <code>key</code>, call {@link IPropertyContainer#get(String, Class)}.
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 *
	 * @param key property name (case insensitive)
	 * @param type type of value to be stored
	 * @param value value to be stored
	 */
	<T> void set(final String key, final Type type, final T value);

}
