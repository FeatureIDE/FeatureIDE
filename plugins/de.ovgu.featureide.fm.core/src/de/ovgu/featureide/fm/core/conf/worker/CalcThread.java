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
package de.ovgu.featureide.fm.core.conf.worker;

import java.util.ArrayList;
import java.util.List;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.conf.FeatureGraph;
import de.ovgu.featureide.fm.core.conf.nodes.Variable;
import de.ovgu.featureide.fm.core.conf.nodes.VariableConfiguration;
import de.ovgu.featureide.fm.core.conf.worker.base.AWorkerThread;

/**
 * TODO description
 * 
 * @author Sebastian Krieter
 */
public class CalcThread extends AWorkerThread<Integer> {

	private final FeatureGraph featureGraph;
	private final VariableConfiguration variableConfiguration;
	private final SatSolver solver;
	private final Node fmNode;

	private List<Node> ls = null;

	public CalcThread(FeatureGraph featureGraph, VariableConfiguration variableConfiguration, Node fmNode) {
		this.featureGraph = featureGraph;
		this.variableConfiguration = variableConfiguration;
		this.fmNode = fmNode;
		this.solver = new SatSolver(fmNode, 1000);
	}

	private CalcThread(FeatureGraph featureGraph, VariableConfiguration variableConfiguration, SatSolver solver) {
		this.featureGraph = featureGraph;
		this.variableConfiguration = variableConfiguration;
		this.solver = solver;
		this.fmNode = null;
	}

	public void setLs(List<Node> ls) {
		this.ls = new ArrayList<>(ls);
	}

	@Override
	protected void work(Integer i) {
		final int curIndex = ls.size();
		try {
			ls.add(new Literal(featureGraph.featureArray[i], false));
			if (!solver.isSatisfiable(ls)) {
				variableConfiguration.setVariable(i, Variable.TRUE);
				ls.set(curIndex, new Literal(featureGraph.featureArray[i], true));
			} else {
				ls.set(curIndex, new Literal(featureGraph.featureArray[i], true));
				if (!solver.isSatisfiable(ls)) {
					variableConfiguration.setVariable(i, Variable.FALSE);
					ls.set(curIndex, new Literal(featureGraph.featureArray[i], false));
				} else {
					ls.remove(curIndex);
				}
			}
		} catch (TimeoutException e) {
			FMCorePlugin.getDefault().logError(e);
			ls.remove(curIndex);
		}
	}

	@Override
	public AWorkerThread<Integer> newInstance() {
		return new CalcThread(featureGraph, variableConfiguration, fmNode.clone());
	}

	@Override
	public CalcThread clone() {
		return new CalcThread(featureGraph, variableConfiguration, solver);
	}

}
