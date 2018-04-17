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

import static de.ovgu.featureide.fm.core.localization.StringTable.STARTING_FEATUREIDE_PLUG_IN_;
import static de.ovgu.featureide.fm.core.localization.StringTable.STOPPING_FEATUREIDE_PLUG_IN_;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Plugin;
import org.eclipse.core.runtime.Status;
import org.osgi.framework.BundleContext;

/**
 * A default implementation for non-UI plug-ins within FeatureIDE.
 *
 * @author Thomas Thuem
 */
abstract public class AbstractCorePlugin extends Plugin {

	/**
	 * Returns the plug-in ID as specified at the plug-in manifest.
	 *
	 * @return the plug-in id
	 */
	abstract public String getID();

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
	 */
	@Override
	public void start(BundleContext context) throws Exception {
		super.start(context);
		logInfo(STARTING_FEATUREIDE_PLUG_IN_ + getID() + "'");
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
	 */
	@Override
	public void stop(BundleContext context) throws Exception {
		logInfo(STOPPING_FEATUREIDE_PLUG_IN_ + getID() + "'");
		super.stop(context);
	}

	/**
	 * Convenience method for easy and clean logging. All messages collected by this method will be written to the eclipse log file.
	 *
	 * Messages are only written to the error log, if the debug option is set for this plug-in
	 *
	 * @param message A message that should be written to the eclipse log file
	 */
	public void logInfo(String message) {
		log(IStatus.INFO, message, new Exception());
	}

	/**
	 * Convenience method for easy and clean logging of warnings. All messages collected by this method will be written to the eclipse log file.
	 *
	 * @param message A message that should be written to the eclipse log file
	 */
	public void logWarning(String message) {
		log(IStatus.WARNING, message, new Exception());
	}

	/**
	 * Convenience method for easy and clean logging of exceptions. All messages collected by this method will be written to the eclipse log file. The
	 * exception's stack trace is added to the log as well.
	 *
	 * @param message A message that should be written to the eclipse log file
	 * @param exception Exception containing the stack trace
	 */
	public void logError(String message, Throwable exception) {
		log(IStatus.ERROR, message, exception);
	}

	/**
	 * Convenience method for easy and clean logging of exceptions. All messages collected by this method will be written to the eclipse log file. The
	 * exception's stack trace is added to the log as well.
	 *
	 * @param exception Exception containing the stack trace
	 */
	public void logError(Throwable exception) {
		if (exception != null) {
			logError(exception.getMessage(), exception);
		}
	}

	/**
	 * Logging any kind of message.
	 *
	 * @param severity
	 * @param message
	 * @param exception
	 */
	private void log(int severity, String message, Throwable exception) {
		if (isDebugging()) {
			getLog().log(new Status(severity, getID(), message, exception));
		}
	}

	public void reportBug(int ticket) {
		logWarning("This is a bug. Please report it. See Ticket #" + ticket + ".");
	}

}
