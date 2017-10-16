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
package de.ovgu.featureide.fm.core;

public interface ICorePlugin {

	/**
	 * Returns the plug-in ID as specified at the plug-in manifest.
	 *
	 * @return the plug-in id
	 */
	String getID();

	/**
	 * Convenience method for easy and clean logging. All messages collected by this method will be written to the eclipse log file.
	 *
	 * Messages are only written to the error log, if the debug option is set for this plug-in
	 *
	 * @param message A message that should be written to the eclipse log file
	 */
	void logInfo(String message);

	/**
	 * Convenience method for easy and clean logging of warnings. All messages collected by this method will be written to the eclipse log file.
	 *
	 * @param message A message that should be written to the eclipse log file
	 */
	void logWarning(String message);

	/**
	 * Convenience method for easy and clean logging of exceptions. All messages collected by this method will be written to the eclipse log file. The
	 * exception's stack trace is added to the log as well.
	 *
	 * @param message A message that should be written to the eclipse log file
	 * @param exception Exception containing the stack trace
	 */
	void logError(String message, Throwable exception);

	/**
	 * Convenience method for easy and clean logging of exceptions. All messages collected by this method will be written to the eclipse log file. The
	 * exception's stack trace is added to the log as well.
	 *
	 * @param exception Exception containing the stack trace
	 */
	void logError(Throwable exception);

	void reportBug(int ticket);

}
