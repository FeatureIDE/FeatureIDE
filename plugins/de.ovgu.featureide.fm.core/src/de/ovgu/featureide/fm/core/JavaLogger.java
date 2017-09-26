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

/**
 *
 * @author Sebastian Krieter
 */
public class JavaLogger implements ILogger {

	@Override
	public void logInfo(String message) {
		System.out.println("INFO: " + message);
	}

	@Override
	public void logWarning(String message) {
		System.out.println("WARNING: " + message);
	}

	@Override
	public void logError(String message) {
		System.err.println("ERROR: " + message);
	}

	@Override
	public void logError(String message, Throwable exception) {
		System.err.println("ERROR: " + message);
		exception.printStackTrace(System.err);
	}

	@Override
	public void logError(Throwable exception) {
		if (exception != null) {
			exception.printStackTrace(System.err);
		}
	}

	@Override
	public void reportBug(int ticket) {
		logWarning("This is a bug. Please report it. See Ticket #" + ticket + ".");
	}

}
