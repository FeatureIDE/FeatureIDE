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

import java.util.ArrayList;

import de.ovgu.featureide.fm.core.io.Problem.Severity;

/**
 * List of {@link Problems problems} that arise during read and write operations.
 *
 * @see IPersistentFormat
 *
 * @author Sebastian Krieter
 */
public class ProblemList extends ArrayList<Problem> {

	private static final long serialVersionUID = -8296890463897407370L;

	/**
	 * Checks whether a given list of problems contains at least one problem with the specified or a greater severity level.
	 *
	 * @param problems The problem list.
	 * @param minimumLevel The minimum severity level (one of {@link Severity#INFO}, {@link Severity#WARNING}, or {@link Severity#ERROR}).
	 *
	 * @return {@code true} if the list contains a problem with severity at the given minimum level or above, {@code false} otherwise.
	 */
	public boolean checkSeverity(Severity minimumLevel) {
		for (final Problem problem : this) {
			if (problem.severity.getLevel() >= minimumLevel.getLevel()) {
				return true;
			}
		}
		return false;
	}

	public ProblemList getErrors() {
		return getProblemType(Severity.ERROR.getLevel());
	}

	public ProblemList getWarnings() {
		return getProblemType(Severity.WARNING.getLevel());
	}

	public ProblemList getProblemType(int level) {
		final ProblemList problemList = new ProblemList();
		for (final Problem problem : this) {
			if (problem.severity.getLevel() == level) {
				problemList.add(problem);
			}
		}
		return problemList;
	}

	public boolean containsError() {
		return checkSeverity(Severity.ERROR);
	}

	public boolean containsWarning() {
		return checkSeverity(Severity.WARNING);
	}

}
