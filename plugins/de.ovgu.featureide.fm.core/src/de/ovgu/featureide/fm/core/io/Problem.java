/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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

	public Problem(Throwable throwable) {
		this.message = throwable.getMessage();
		this.line = 0;
		this.severity = Severity.ERROR;
	}

	public Problem(String message, int line) {
		this.message = message;
		this.line = line;
		this.severity = Severity.WARNING;
	}

	public Problem(String message, int line, Severity severity) {
		this.message = message;
		this.line = line;
		this.severity = severity;
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
