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
package de.ovgu.featureide.fm.core.io;

import de.ovgu.featureide.fm.core.Logger;

/**
 * Saves a warning with a line number where it occurred.
 *
 * @see ProblemList
 *
 * @author Thomas Thuem
 * @author Sebastian Krieter
 */
public class Problem {

	public static enum Severity {
		INFO(0), WARNING(1), ERROR(2);

		private final int level;

		private Severity(int level) {
			this.level = level;
		}

		public int getLevel() {
			return level;
		}
	}

	public final Severity severity;

	public final String message;

	public final int line;

	public final Throwable error;

	public Problem(Throwable throwable) {
		this(throwable.getMessage(), 1, Severity.ERROR, throwable);
	}

	public Problem(Throwable throwable, int line) {
		this(throwable.getMessage(), line, Severity.ERROR, throwable);
	}

	public Problem(String message, int line) {
		this(message, line, Severity.WARNING, null);
	}

	public Problem(String message, int line, Throwable throwable) {
		this(message, line, Severity.ERROR, throwable);
	}

	public Problem(String message, int line, Severity severity) {
		this(message, line, severity, null);
	}

	protected Problem(String message, int line, Severity severity, Throwable error) {
		this.message = message;
		this.line = line;
		this.severity = severity;
		this.error = error;
		if (error != null) {
			Logger.logError(message, error);
		} else {
			switch (severity) {
			case ERROR:
				Logger.logError(message);
				break;
			case INFO:
				Logger.logInfo(message);
				break;
			case WARNING:
				Logger.logWarning(message);
				break;
			default:
				throw new RuntimeException();
			}
		}
	}

	@Override
	public String toString() {
		return "Problem(" + severity + ") " + message;
	}

	public Severity getSeverity() {
		return severity;
	}

	public String getMessage() {
		return message;
	}

	public int getLine() {
		return line;
	}

}
