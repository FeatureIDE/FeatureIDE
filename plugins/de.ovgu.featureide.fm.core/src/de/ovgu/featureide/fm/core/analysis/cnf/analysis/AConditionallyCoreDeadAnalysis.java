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
package de.ovgu.featureide.fm.core.analysis.cnf.analysis;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.ISatSolver;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds core and dead features under certain assumptions. Regularly returns intermediate results to a given monitor.
 *
 * @author Sebastian Krieter
 */
public abstract class AConditionallyCoreDeadAnalysis extends AbstractAnalysis<LiteralSet> {

	public static class IntermediateResult {

		private final int var;
		private final Selection selection;

		public IntermediateResult(int var, Selection selection) {
			this.var = var;
			this.selection = selection;
		}

		public int getVar() {
			return var;
		}

		public Selection getSelection() {
			return selection;
		}
	}

	protected IMonitor<LiteralSet> monitor;
	protected int[] fixedVariables;
	protected int[] variableOrder;
	protected int newCount;

	public AConditionallyCoreDeadAnalysis(ISatSolver solver) {
		super(solver);
		resetFixedFeatures();
	}

	public AConditionallyCoreDeadAnalysis(CNF satInstance) {
		super(satInstance);
		resetFixedFeatures();
	}

	@Override
	protected LiteralSet analyze(IMonitor<LiteralSet> monitor) throws Exception {
		this.monitor = monitor;
		return null;
	}

	public void setFixedFeatures(int[] fixedVariables, int newCount) {
		this.fixedVariables = fixedVariables;
		this.newCount = newCount;
	}

	public void setVariableOrder(int[] variableOrder) {
		this.variableOrder = variableOrder;
	}

	public void resetFixedFeatures() {
		fixedVariables = new int[0];
		newCount = 0;
	}

	public void updateModel(final int[] model1, int[] model2) {
		for (int i = 0; i < model1.length; i++) {
			final int x = model1[i];
			final int y = model2[i];
			if ((x != 0) && (x != y)) {
				model1[i] = 0;
				monitor.step();
			}
		}
	}

	protected static int countNegative(int[] model) {
		int count = 0;
		for (int i = 0; i < model.length; i++) {
			count += model[i] >>> (Integer.SIZE - 1);
		}
		return count;
	}

}
