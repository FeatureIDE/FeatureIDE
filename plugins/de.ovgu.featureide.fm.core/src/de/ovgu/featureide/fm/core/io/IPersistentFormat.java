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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.io;

import java.nio.file.Path;

import de.ovgu.featureide.fm.core.IExtension;

/**
 * Interface for reading and writing data from and to arbitrary objects.
 *
 * @author Sebastian Krieter
 */
public interface IPersistentFormat<T> extends IExtension {

	/**
	 * Parses the contents of the given source and transfers all information onto the given object. The object is intended to be completely overridden. A
	 * subclass may try to reset the information already stored inside the object, but is not obligated to do so. Thus, if possible an empty object should be
	 * passed here.
	 *
	 * @param object the object to write the information into.
	 * @param source the source content.
	 * @return A list of {@link Problem problems} that occurred during the parsing process.
	 *
	 * @see #supportsRead()
	 */
	ProblemList read(T object, CharSequence source);

	/**
	 * Parses the contents of the given source and transfers all information onto the given object. The object is intended to be completely overridden. A
	 * subclass may try to reset the information already stored inside the object, but is not obligated to do so. Thus, if possible an empty object should be
	 * passed here.
	 *
	 * @param object the object to write the information into.
	 * @param source the source content.
	 * @param path the path of the source file.
	 * @return A list of {@link Problem problems} that occurred during the parsing process.
	 *
	 * @see #supportsRead()
	 */
	default ProblemList read(T object, CharSequence source, Path path) {
		return read(object, source);
	}

	/**
	 * Writes the information of an object to a string. (Which information are considered is specified by the implementing class).
	 *
	 * @param object the object to get the information from.
	 * @return A string representing the object in this format.
	 *
	 * @see #supportsWrite()
	 */
	String write(T object);

	/**
	 * Returns the file extension for this format. (Without a leading ".")
	 *
	 * @return A string representing this format's file extension.
	 */
	String getSuffix();

	/**
	 * Returns a meaningful name for this format. This is intended for user interfaces (e.g., in dialogs).
	 *
	 * @return A string representing this format's name.
	 */
	String getName();

	/**
	 * Returns an instance of this format. Clients should always call this method before calling {@link #read(Object, CharSequence)} or {@link #write(Object)}
	 * and call these methods the returned value to avoid any unintended concurrent access.<br><br> <b>Example</b> <code> IPersistentFormat&lt;?&gt; format =
	 * getFormat(); format.getInstance().write(new Object())</code> Implementing classes may return {@code this}, if {@code read} and {@code write} are
	 * implemented in a static fashion (i.e., do not use any non-static fields).
	 *
	 * @return An instance of this format.
	 */
	IPersistentFormat<T> getInstance();

	/**
	 * Returns whether this format supports the {@link #read(Object, CharSequence)} operation.
	 *
	 * @return {@code true} if {@code read} is allowed by this format, {@code false} otherwise.
	 */
	boolean supportsRead();

	/**
	 * Returns whether this format supports the {@link #write(Object)} operation.
	 *
	 * @return {@code true} if {@code write} is allowed by this format, {@code false} otherwise.
	 */
	boolean supportsWrite();

	/**
	 * Returns whether this format supports the parsing of the given content.
	 *
	 * @param content The content to be parsed.
	 * @return {@code true} if the content should be parsable by this format, {@code false} otherwise.
	 */
	boolean supportsContent(CharSequence content);

	/**
	 * Returns whether this format supports the parsing of the given content.
	 *
	 * @param reader The content to be parsed.
	 * @return {@code true} if the content should be parsable by this format, {@code false} otherwise.
	 */
	boolean supportsContent(LazyReader reader);

}
