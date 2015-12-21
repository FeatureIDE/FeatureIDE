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
package de.ovgu.featureide.fm.core.io;

import org.eclipse.core.resources.IMarker;

/**
 * Saves a warning with a line number where it occurred.
 * 
 * @author Thomas Thuem
 */
public class Problem {

	public final int severity;

	public final String message;

	public final int line;

	public Problem(Throwable throwable) {
		this.message = throwable.getMessage();
		this.line = 0;
		this.severity = IMarker.SEVERITY_ERROR;
	}

	public Problem(String message, int line) {
		this.message = message;
		this.line = line;
		this.severity = IMarker.SEVERITY_WARNING;
	}

	public Problem(String message, int line, int severity) {
		this.message = message;
		this.line = line;
		this.severity = severity;
	}

	@Override
	public String toString() {
		return "Problem(" + severity + ") " + message;
	}
	
	/**
	 * Checks whether a given list of problems contains at least one problem with the specified or a greater severity level.
	 * 
	 * @param problems The problem list.
	 * @param minimumLevel The minimum severity level
	 * 		(one of {@link IMarker#SEVERITY_INFO}, {@link IMarker#SEVERITY_WARNING}, or {@link IMarker#SEVERITY_ERROR}).
	 * 
	 * @return {@code true} if the list contains a problem with severity at the given minimum level or above, {@code false} otherwise.
	 */
	public static boolean checkSeverity(Iterable<Problem> problems, int minimumLevel) {
		for (Problem modelWarning : problems) {
			if (modelWarning.severity >= minimumLevel) {
				return true;
			}
		}
		return false;
	}

}
