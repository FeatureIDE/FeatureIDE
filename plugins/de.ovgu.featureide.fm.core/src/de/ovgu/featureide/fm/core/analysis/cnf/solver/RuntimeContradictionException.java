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
package de.ovgu.featureide.fm.core.analysis.cnf.solver;

/**
 * Exception thrown when a {@link solver ISatSolver} detects an obvious contradiction when adding new clauses.<br/> Doesn't need to be caught explicitly.
 *
 * @author Sebastian Krieter
 */
public class RuntimeContradictionException extends RuntimeException {

	private static final long serialVersionUID = -4951752949650801254L;

	public RuntimeContradictionException() {
		super();
	}

	public RuntimeContradictionException(String message) {
		super(message);
	}

	public RuntimeContradictionException(Throwable cause) {
		super(cause);
	}

	public RuntimeContradictionException(String message, Throwable cause) {
		super(message, cause);
	}

}
