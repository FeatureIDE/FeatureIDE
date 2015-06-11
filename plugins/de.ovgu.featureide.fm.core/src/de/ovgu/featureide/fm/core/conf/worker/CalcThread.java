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
import de.ovgu.featureide.fm.core.conf.IConfigurationChanger;
import de.ovgu.featureide.fm.core.conf.nodes.Variable;
import de.ovgu.featureide.fm.core.conf.worker.base.AWorkerThread;
import de.ovgu.featureide.fm.core.job.WorkMonitor;

/**
 * TODO description
 * 
 * @author Sebastian Krieter
 */
public class CalcThread extends AWorkerThread<Integer> {

	private static class SharedObjects {
		private final FeatureGraph featureGraph;
		private final IConfigurationChanger variableConfiguration;
		private final Node fmNode;

		private List<Literal> knownLiterals = null;
		private Literal l = null;

		public SharedObjects(FeatureGraph featureGraph, IConfigurationChanger variableConfiguration, Node fmNode) {
			this.featureGraph = featureGraph;
			this.variableConfiguration = variableConfiguration;
			this.fmNode = fmNode;
		}
	}

	private final SimpleSatSolver solver;
	private final SharedObjects sharedObjects;

	public CalcThread(FeatureGraph featureGraph, IConfigurationChanger variableConfiguration, Node fmNode) {
		super(new WorkMonitor());
		this.sharedObjects = new SharedObjects(featureGraph, variableConfiguration, fmNode);
		this.solver = new SimpleSatSolver(fmNode, 1000);
	}

	private CalcThread(CalcThread oldThread) {
		super(oldThread);
		this.sharedObjects = oldThread.sharedObjects;
		this.solver = new SimpleSatSolver(oldThread.sharedObjects.fmNode, 1000);
	}

	public void setKnownLiterals(List<Literal> knownLiterals, Literal l) {
		sharedObjects.knownLiterals = knownLiterals;
		sharedObjects.l = l;
	}

	@Override
	protected boolean beforeWork() {
		this.solver.setBackbone(sharedObjects.knownLiterals, sharedObjects.l);
		return super.beforeWork();
	}

	@Override
	protected void work(Integer i) {
		final byte value = solver.getValueOf(new Literal(sharedObjects.featureGraph.featureArray[i]));
		switch (value) {
		case 1:
			sharedObjects.variableConfiguration.setNewValue(i, Variable.TRUE, false);
			break;
		case -1:
			sharedObjects.variableConfiguration.setNewValue(i, Variable.FALSE, false);
			break;
		default:
			sharedObjects.variableConfiguration.setNewValue(i, Variable.UNDEFINED, false);
			break;
		}
	}

	@Override
	protected AWorkerThread<Integer> newThread() {
		return new CalcThread(this);
	}

}
