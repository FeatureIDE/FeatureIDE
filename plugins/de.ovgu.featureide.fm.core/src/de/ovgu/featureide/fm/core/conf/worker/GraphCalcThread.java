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
import org.prop4j.MultiThreadSatSolver;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.conf.IConfigurationChanger;
import de.ovgu.featureide.fm.core.conf.nodes.Variable;
import de.ovgu.featureide.fm.core.conf.worker.base.AWorkerThread;
import de.ovgu.featureide.fm.core.job.WorkMonitor;

/**
 * TODO description
 * 
 * @author Sebastian Krieter
 */
public class GraphCalcThread extends AWorkerThread<Integer> {

	private static class SharedObjects {

		private final MultiThreadSatSolver solver;
		private final String[] featureArray;
		private final IConfigurationChanger variableConfiguration;
		private final int numberOfSolvers;

		private int lastSolverID = 0;
		private List<Literal> knownLiterals = null;

		public SharedObjects(String[] featureArray, IConfigurationChanger variableConfiguration, Node fmNode, int numberOfSolvers) {
			this.featureArray = featureArray;
			this.variableConfiguration = variableConfiguration;
			this.numberOfSolvers = numberOfSolvers;
			this.solver = new MultiThreadSatSolver(fmNode, 1000, numberOfSolvers, false);
		}

	}

	private final int id;
	private final SharedObjects sharedObjects;

	public GraphCalcThread(String[] featureArray, IConfigurationChanger variableConfiguration, Node fmNode) {
		this(featureArray, variableConfiguration, fmNode, NUMBER_OF_THREADS);
	}

	public GraphCalcThread(String[] featureArray, IConfigurationChanger variableConfiguration, Node fmNode, int numberOfSolvers) {
		super(new WorkMonitor());
		sharedObjects = new SharedObjects(featureArray, variableConfiguration, fmNode, numberOfSolvers);
		this.id = sharedObjects.lastSolverID;
	}

	private GraphCalcThread(GraphCalcThread oldThread) {
		super(oldThread);
		this.sharedObjects = oldThread.sharedObjects;
		this.id = ++oldThread.sharedObjects.lastSolverID;
	}

	public void setKnownLiterals(List<Literal> knownLiterals, Literal l) {
		sharedObjects.knownLiterals = knownLiterals;
	}

	public void setKnownLiterals(List<Literal> knownLiterals) {
		setKnownLiterals(knownLiterals, null);
	}

	@Override
	public void start() {
		startWork();
	}

	@Override
	public void start(int numberOfThreads) {
		startWork();
	}

	private void startWork() {
		sharedObjects.solver.setLiterals(sharedObjects.knownLiterals);
		super.start(sharedObjects.numberOfSolvers);
	}

	@Override
	protected boolean beforeWork() {
		sharedObjects.solver.initSolver(id);
		sharedObjects.solver.setBackbone(id);
		return super.beforeWork();
	}

	@Override
	protected void work(Integer i) {
		final byte value = sharedObjects.solver.getValueOf(new Literal(sharedObjects.featureArray[i]), id);
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
	protected GraphCalcThread newThread() {
		return new GraphCalcThread(this);
	}

}
