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

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;

/**
 *
 * @author Thomas Thuem
 */
public class EclipseLogger implements ILogger {

	/**
	 * Convenience method for easy and clean logging. All messages collected by this method will be written to the eclipse log file.
	 *
	 * Messages are only written to the error log, if the debug option is set for this plug-in
	 *
	 * @param message A message that should be written to the eclipse log file
	 */
	@Override
	public void logInfo(String message) {
		log(IStatus.INFO, message, new Exception());
	}

	/**
	 * Convenience method for easy and clean logging of warnings. All messages collected by this method will be written to the eclipse log file.
	 *
	 * @param message A message that should be written to the eclipse log file
	 */
	@Override
	public void logWarning(String message) {
		log(IStatus.WARNING, message, new Exception());
	}

	@Override
	public void logError(String message) {
		log(IStatus.ERROR, message, new Exception());
	}

	/**
	 * Convenience method for easy and clean logging of exceptions. All messages collected by this method will be written to the eclipse log file. The
	 * exception's stack trace is added to the log as well.
	 *
	 * @param message A message that should be written to the eclipse log file
	 * @param exception Exception containing the stack trace
	 */
	@Override
	public void logError(String message, Throwable exception) {
		log(IStatus.ERROR, message, exception);
	}

	/**
	 * Convenience method for easy and clean logging of exceptions. All messages collected by this method will be written to the eclipse log file. The
	 * exception's stack trace is added to the log as well.
	 *
	 * @param exception Exception containing the stack trace
	 */
	@Override
	public void logError(Throwable exception) {
		if (exception != null) {
			logError(exception.getMessage(), exception);
		}
	}

	@Override
	public void reportBug(int ticket) {
		logWarning("This is a bug. Please report it. See Ticket #" + ticket + ".");
	}

	/**
	 * Logging any kind of message.
	 */
	private void log(int severity, String message, Throwable exception) {
		if (FMCorePlugin.getDefault().isDebugging()) {
			FMCorePlugin.getDefault().getLog().log(new Status(severity, PluginID.PLUGIN_ID, message, exception));
		}
	}

}
