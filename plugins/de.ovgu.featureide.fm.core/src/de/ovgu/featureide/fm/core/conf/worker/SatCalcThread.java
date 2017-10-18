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
package de.ovgu.featureide.fm.core.conf.worker;

import java.util.List;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.SimpleSatSolver;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.conf.IConfigurationChanger;
import de.ovgu.featureide.fm.core.conf.IFeatureGraph;
import de.ovgu.featureide.fm.core.conf.nodes.Variable;
import de.ovgu.featureide.fm.core.conf.worker.base.AWorkerThread;
import de.ovgu.featureide.fm.core.job.monitor.NullMonitor;

/**
 * TODO description
 *
 * @author Sebastian Krieter
 */
public class SatCalcThread extends AWorkerThread<Integer> {

	private static class SharedObjects {

		private final IConfigurationChanger variableConfiguration;
		private final Node fmNode;
		private final String[] featureNames;

		private List<Literal> knownLiterals = null;
		private Literal l = null;

		public SharedObjects(IFeatureGraph featureGraph, IConfigurationChanger variableConfiguration, Node fmNode) {
			this.variableConfiguration = variableConfiguration;
			this.fmNode = fmNode;
			featureNames = FeatureUtils.getFeaturesFromFeatureGraph(featureGraph);
		}
	}

	private final SimpleSatSolver solver;
	private final SharedObjects sharedObjects;

	public SatCalcThread(IFeatureGraph featureGraph, IConfigurationChanger variableConfiguration, Node fmNode) {
		super(new NullMonitor());
		sharedObjects = new SharedObjects(featureGraph, variableConfiguration, fmNode);
		solver = new SimpleSatSolver(fmNode, 1000);
	}

	private SatCalcThread(SatCalcThread oldThread) {
		super(oldThread);
		sharedObjects = oldThread.sharedObjects;
		solver = new SimpleSatSolver(oldThread.sharedObjects.fmNode, 1000);
	}

	public void setKnownLiterals(List<Literal> knownLiterals, Literal l) {
		sharedObjects.knownLiterals = knownLiterals;
		sharedObjects.l = l;
	}

	@Override
	protected boolean beforeWork() {
		solver.setBackbone(sharedObjects.knownLiterals, sharedObjects.l);
		return super.beforeWork();
	}

	@Override
	protected void work(Integer i) {
		final byte value = solver.getValueOf(new Literal(sharedObjects.featureNames[i]));
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
		return new SatCalcThread(this);
	}

}
