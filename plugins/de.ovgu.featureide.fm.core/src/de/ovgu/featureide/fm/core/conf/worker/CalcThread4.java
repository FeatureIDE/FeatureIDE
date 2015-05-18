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

import java.util.List;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.SimpleSatSolver;

import de.ovgu.featureide.fm.core.conf.FeatureGraph;
import de.ovgu.featureide.fm.core.conf.SatConfChanger;
import de.ovgu.featureide.fm.core.conf.worker.base.AWorkerThread;

/**
 * TODO description
 * 
 * @author Sebastian Krieter
 */
public class CalcThread4 extends AWorkerThread<Integer> implements ISatThread {

	private final FeatureGraph featureGraph;
	private final SatConfChanger variableConfiguration;
	private final SimpleSatSolver solver;
	private final Node fmNode;

	public CalcThread4(FeatureGraph featureGraph, SatConfChanger variableConfiguration, Node fmNode) {
		this.featureGraph = featureGraph;
		this.variableConfiguration = variableConfiguration;
		this.fmNode = fmNode;
		this.solver = new SimpleSatSolver(fmNode, 1000);
	}

	private CalcThread4(FeatureGraph featureGraph, SatConfChanger variableConfiguration, SimpleSatSolver solver) {
		this.featureGraph = featureGraph;
		this.variableConfiguration = variableConfiguration;
		this.solver = solver;
		this.fmNode = null;
	}

	public void setKnownLiterals(List<Node> knownLiterals) {
		this.solver.seBackbone(knownLiterals);
	}

	@Override
	protected void work(Integer i) {
		final byte value = solver.getValueOf(new Literal(featureGraph.featureArray[i]));
		switch (value) {
		case  1:
			variableConfiguration.set(i, true);
			break;
		case -1:
			variableConfiguration.set(i, false);
			break;
		default:
			break;
		}
	}

	@Override
	public AWorkerThread<Integer> newInstance() {
		return new CalcThread4(featureGraph, variableConfiguration, fmNode.clone());
	}

	@Override
	public CalcThread4 clone() {
		return new CalcThread4(featureGraph, variableConfiguration, solver);
	}

}
