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
package org.prop4j.solver;

import static org.sat4j.core.LiteralsUtils.negLit;
import static org.sat4j.core.LiteralsUtils.posLit;
import static org.sat4j.core.LiteralsUtils.var;

import org.sat4j.minisat.core.IPhaseSelectionStrategy;

public class FixedLiteralSelectionStrategy implements IPhaseSelectionStrategy {

	private static final long serialVersionUID = -1687370944480053808L;

	private final int[] model, phase;

	public FixedLiteralSelectionStrategy(int[] model, boolean reverse) {
		this.model = model;
		phase = new int[model.length + 1];
		if (reverse) {
			for (int i = 0; i < model.length; i++) {
				phase[i + 1] = model[i] >= 0 ? negLit(i + 1) : posLit(i + 1);
			}
		} else {
			for (int i = 0; i < model.length; i++) {
				phase[i + 1] = model[i] <= 0 ? negLit(i + 1) : posLit(i + 1);
			}
		}
	}

	@Override
	public void updateVar(int p) {}

	@Override
	public void assignLiteral(int p) {
		final int var = var(p);
		if (model[var - 1] == 0) {
			phase[var] = p;
		}
	}

	@Override
	public void updateVarAtDecisionLevel(int q) {}

	@Override
	public void init(int nlength) {}

	@Override
	public void init(int var, int p) {}

	@Override
	public int select(int var) {
		return phase[var];
	}

}
