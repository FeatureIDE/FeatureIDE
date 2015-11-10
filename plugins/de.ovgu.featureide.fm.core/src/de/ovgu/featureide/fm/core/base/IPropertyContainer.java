/* objectIDE - A Framework for object-Oriented Software Development
 * Copyright (C) 2005-2015  objectIDE team, University of Magdeburg, Germany
 *
 * This file is part of objectIDE.
 * 
 * objectIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * objectIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with objectIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://objectide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.core.base;

import java.util.Collection;
import java.util.NoSuchElementException;
import java.util.Set;

/**
 * Classes implementing <code>IPropertyContainer</code> act objects that can be enriched with arbitrary user-defined values
 * by key-value mappings ("properties"). 
 * 
 * @author Marcus Pinencke
 * @since 3.0
 */
public interface IPropertyContainer {

	/**
	 * Thrown by <code>IPropertyContainer</code> implementations indicating a request for a unknown property, e.g., by
	 * reading from an unknown <code>key</code>
	 * 
	 * @author Marcus Pinencke
	 * @since 3.0
	 */
	class NoSuchPropertyException extends NoSuchElementException {
		private static final long serialVersionUID = 6923332230285211910L;

		public NoSuchPropertyException(String key) {
			super("The container \"\" does not contain a property with the given key:" + key);
		}
	}

	/**
	 * Defines the behavior for {@link IPropertyContainer#setProperty(String, Class, Object, KeyConflictPolicy,ValueProtection)} when a key-name conflict
	 * occurs.
	 * Either the value associated with a given key <i>k</i> is updated or changes are be discarded. Alternatively, an exception can be thrown indicating a
	 * conflict.
	 * An exception will be thrown in any case, if the value to be overwritten behind <i>k</i> is protected and <code>FORCE_OVERWRITE_OLD_VALUE</code> is not
	 * used.
	 * <br/>
	 * <br/>
	 * Whenever an exception will be automatically thrown by using <code>OVERWRITE_OLD_VALUE</code> instead of <code>FORCE_OVERWRITE_OLD_VALUE</code> depends on
	 * the value {@link IPropertyContainer.ValueProtection} attribute assigned the the value to be overwritten that was specified at it's creation during
	 * {@link IPropertyContainer#setProperty(String, Class, Object, KeyConflictPolicy,ValueProtection)} call.
	 * 
	 * @see ValueProtection
	 * @see IPropertyContainer#setProperty(String, Class, Object, KeyConflictPolicy,ValueProtection)
	 * 
	 * @author Marcus Pinnecke
	 * @since 3.0
	 */
	public static enum KeyConflictPolicy {
		OVERWRITE_OLD_VALUE, FORCE_OVERWRITE_OLD_VALUE, KEEP_OLD_VALUE, THROW_EXCEPTION
	}

	/**
	 * Defines the value protection level for conflicting writes if
	 * {@link IPropertyContainer#setProperty(String, Class, Object, KeyConflictPolicy,ValueProtection)} is called on the related key.
	 * Storing a values behind a key can be either temporary (which will not be saved to disc) or persistent (which will be saved to disc as soon as possible).
	 * Moreover, a property can be either with normal (overwritable) protection level or with read only protection level (which cannot be changed unless
	 * <code>FORCE_OVERWRITE_OLD_VALUE</code> of {@link IPropertyContainer.KeyConflictPolicy} is used).
	 * <br/>
	 * <br/>
	 * The protection level is per-object key centric. This means, the protection level of a value <i>v</i> behind a key <i>k</i> of a object <i>f</i> does
	 * not influence the protection level of another but identical value <i>v'</i> behind another key <i>k'</i> of any other object <i>f'</i> (including
	 * <i>f</i>)
	 * 
	 * @see KeyConflictPolicy
	 * @see IPropertyContainer#setProperty(String, Class, Object, KeyConflictPolicy,ValueProtection)
	 * 
	 * @author Marcus Pinnecke
	 * @since 3.0
	 */
	public static enum ValueProtection {
		NORMAL_TEMPORARY, READ_ONLY_TEMPORARY, NORMAL_PERSISTENT, READ_ONLY_PERSISTENT
	}

	/**
	 * Reads a per-object user-defined property identified by a custom <code>key</code>, and returns the stored value if a value was assigned by calling
	 * {@link IPropertyContainer#setProperty(String, Class, Object)} earlier. Properties are stored persistently if {@link ValueProtection#NORMAL_PERSISTENT} or
	 * {@link ValueProtection#READ_ONLY_PERSISTENT} was used when calling
	 * {@link IPropertyContainer#setProperty(String, Class, Object, KeyConflictPolicy, ValueProtection)} or temporarily. The latest (maybe volatile) state will
	 * be taken into account, depending on the call of {@link IPropertyContainer#removeProperty(String)}. If no value was assigned (the
	 * <code>key is unknown</code>), the
	 * <code>defaultValue</code> will be returned.
	 * 
	 * @author Marcus Pinnecke
	 * @since 3.0
	 * 
	 * @see IPropertyContainer#getProperty(String, Class)
	 * @see IPropertyContainer#hasProperty(String)
	 * @see IPropertyContainer#removeProperty(String)
	 * 
	 * @param key property name (case insensitive)
	 * @param type type of returning value
	 * @param defaultValue value to return if no property is set
	 * @return value associated with <code>key</code> if set, <code>defaultValue</code> otherwise
	 */
	<T> T getProperty(final String key, final Class<T> type, final T defaultValue);

	/**
	 * Reads a per-object user-defined property identified by a custom <code>key</code>, and returns the stored value if a value was assigned by calling
	 * {@link IPropertyContainer#setProperty(String, Class, Object)} earlier. Properties are stored persistently such that an assignment will be alive as long
	 * as it was not removed by calling {@link IPropertyContainer#removeProperty(String)}. If no value was assigned (the <code>key is unknown</code>), a
	 * <code>NoSuchPropertyException</code> will be thrown.
	 * 
	 * @see IPropertyContainer#getProperty(String, Class, Object)
	 * @see IPropertyContainer#hasProperty(String)
	 * @see IPropertyContainer#removeProperty(String)
	 * 
	 * @author Marcus Pinnecke
	 * @since 3.0
	 * 
	 * @param key property name (case insensitive)
	 * @param type type of returning value
	 * @param defaultValue value to return if no property is set
	 * @return value associated with <code>key</code> if set. If <code>key</code> is not known, throws <code>NoSuchPropertyException</code>.
	 */
	<T> T getProperty(final String key, final Class<T> type) throws NoSuchPropertyException;

	/**
	 * Checks if this object contains a property associated with the given <code>key</code>. Returns <code>true</code> if at some point earlier
	 * {@link IPropertyContainer#setProperty(String, Class, Object)} was called with the corresponding <code>key</code>. Properties are stored persistently such
	 * that an assignment will be alive as long as it was not removed by calling {@link IPropertyContainer#removeProperty(String)}, and, hence, <code>key</code>
	 * will be alive. If no property is associated to <code>key</code> the method will return <code>false</code>.
	 * 
	 * @author Marcus Pinnecke
	 * @since 3.0
	 * 
	 * @param key property name (case insensitive)
	 * @return <b>true</b> if the object contains a property associated to <code>key</code>, <b>false</b> otherwise.
	 */
	boolean hasProperty(final String key);

	/**
	 * Checks if the property associated with <code>key</code> has the value protection level <code>attribute</code>.
	 * 
	 * @author Marcus Pinnecke
	 * @since 3.0
	 * 
	 * @param key property name (case insensitive)
	 * @param attribute protection level
	 * @return <b>true</b> when matching <code>attribute</code>, <b>false</b> otherwise
	 * @throws NoSuchPropertyException when this object does not contain a property with name <code>key</code>
	 */
	boolean hasPropertyAttribute(final String key, final ValueProtection attribute) throws NoSuchPropertyException;

	/**
	 * Returns the value protection level for the property associated with <code>key</code> or throws <code>NoSuchPropertyException</code>
	 * when <code>key</code> is unknown.
	 * 
	 * @author Marcus Pinnecke
	 * @since 3.0
	 * 
	 * @param key property name (case insensitive)
	 * @return protection level
	 * @throws NoSuchPropertyException when <code>key</code> is not assigned to any property for this object
	 */
	ValueProtection getPropertyAttribute(final String key) throws NoSuchPropertyException;
	
	/**
	 * Returns a distinct collection of each assigned key for this object in (possible empty) set. Since keys are case-insensitive
	 * it depends on the implementation if the user-defined strings once passed as keys are changed in some way, e.g., by
	 * converting to lower case strings.
	 * 
	 * @return all keys of properties assigned to this object
	 */
	Set<String> getPropertyKeySet();

	/**
	 * Removes a per-object user-defined property identified by a custom <code>key</code> and value assigned by calling
	 * {@link IPropertyContainer#setProperty(String, Class, Object)} earlier. Properties are stored persistently such
	 * that an assignment will be alive as long as it this method does not remove the property. If this object does not contain any
	 * property associated to <code>key</code>, a <code>NoSuchPropertyException</code> will be thrown.
	 * 
	 * @author Marcus Pinnecke
	 * @since 3.0
	 * 
	 * @see IPropertyContainer#hasProperty(String)
	 * @see IPropertyContainer#setProperty(String)
	 * 
	 * @param key property name (case insensitive)
	 * @throws NoSuchPropertyException
	 */
	void removeProperty(final String key) throws NoSuchPropertyException;

	/**
	 * Sets a per-object user-defined property consisting of a <code>values</code> associated with a user-defined <code>key</code>. If <code>key</code> is
	 * already set, the behavior of this method depends on the <code>KeyConflictPolicy</code>. If it is possible to store the value, the
	 * <code>ValueProtection</code>
	 * attribute controls how other calls of {@link IPropertyContainer#setProperty(String, Class, Object, KeyConflictPolicy, ValueProtection)} will behave when
	 * a conflicting write on the same <code>key</code> is performed. In general, a property can be protected from changes using
	 * {@link IPropertyContainer.ValueProtection#READ_ONLY_PERSISTENT} or {@link IPropertyContainer.ValueProtection#READ_ONLY_TEMPORARY} which only can be
	 * ignored
	 * by the next call of {@link IPropertyContainer#setProperty(String, Class, Object, KeyConflictPolicy, ValueProtection)} with
	 * {@link IPropertyContainer.KeyConflictPolicy#FORCE_OVERWRITE_OLD_VALUE} permission.
	 * <br/>
	 * <br/>
	 * Properties are stored persistently such that an assignment will be alive as long as it was not removed by calling
	 * {@link IPropertyContainer#removeProperty(String)}, or
	 * temporarily such that their state fall back to the last persistent state.
	 * <br/>
	 * <br/>
	 * To receive the value behind a <code>key</code>, call {@link IPropertyContainer#getProperty(String, Class)}.
	 * 
	 * @author Marcus Pinnecke
	 * @since 3.0
	 * 
	 * @param key property name (case insensitive)
	 * @param type type of value to be stored
	 * @param value value to be stored
	 * @param keyConflictPolicy controls the behavior of this method for conflicting key writes
	 * @param valueProtectionAttribute controls the protection level for conflicting key writes of other methods
	 */
	<T> void setProperty(final String key, final Class<T> type, final T value, final KeyConflictPolicy keyConflictPolicy,
			final ValueProtection valueProtectionAttribute);

}
