/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import static org.sat4j.core.LiteralsUtils.negLit;
import static org.sat4j.core.LiteralsUtils.posLit;

import java.util.Random;

import org.sat4j.minisat.core.IPhaseSelectionStrategy;

/**
 * Uses a sample of configurations to achieve a phase selection that corresponds to a uniform distribution of configurations in the configuration space.
 *
 * @author Sebastian Krieter
 */
public class RandomSelectionStrategy implements IPhaseSelectionStrategy {

	private static final long serialVersionUID = 1L;

	public final Random RAND = new Random(123456789);

	@Override
	public void assignLiteral(int p) {}

	@Override
	public void init(int nlength) {}

	@Override
	public void init(int var, int p) {}

	@Override
	public int select(int var) {
		return RAND.nextBoolean() ? posLit(var) : negLit(var);
	}

	@Override
	public void updateVar(int p) {}

	@Override
	public void updateVarAtDecisionLevel(int q) {}

	@Override
	public String toString() {
		return "random phase selection";
	}

}
