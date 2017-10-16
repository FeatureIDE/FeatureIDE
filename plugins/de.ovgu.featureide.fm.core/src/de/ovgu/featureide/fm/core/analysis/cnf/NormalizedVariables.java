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
package de.ovgu.featureide.fm.core.analysis.cnf;

/**
 * Represents an instance of a satisfiability problem in CNF.<br/> Use a {@link ISatSolverProvider solver provider} or the {@link #getSolver()} method to get a
 * {@link BasicSolver solver} for this problem.
 *
 * @author Sebastian Krieter
 */
public class NormalizedVariables extends Variables {

	private static final long serialVersionUID = 3034547724030374119L;

	protected final Variables orgVariables;

	public NormalizedVariables(Variables orgVariables) {
		super(orgVariables);
		this.orgVariables = orgVariables;
	}

	public NormalizedVariables(NormalizedVariables oldNormalizedVaribles) {
		super(oldNormalizedVaribles);
		orgVariables = oldNormalizedVaribles.orgVariables;
	}

}
