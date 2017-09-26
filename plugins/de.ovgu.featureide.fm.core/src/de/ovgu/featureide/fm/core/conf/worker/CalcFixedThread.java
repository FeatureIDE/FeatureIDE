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

import java.util.ArrayList;
import java.util.List;

import org.prop4j.Literal;
import org.prop4j.MultiThreadSatSolver;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.conf.worker.base.AWorkerThread;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.NullMonitor;

/**
 * TODO description
 *
 * @author Sebastian Krieter
 */
public class CalcFixedThread extends AWorkerThread<String> {

	private static class SharedObjects {

		private final MultiThreadSatSolver solver;
		private final ArrayList<Literal> fixedLiteralsList = new ArrayList<>();
		private final int numberOfSolvers;

		private int lastSolverID = 0;

		public SharedObjects(Node fmNode, int numberOfSolvers) {
			this.numberOfSolvers = numberOfSolvers;
			solver = new MultiThreadSatSolver(fmNode, 1000, numberOfSolvers, false);
		}

	}

	private final int id;
	private final SharedObjects sharedObjects;

	public CalcFixedThread(Node fmNode) {
		this(fmNode, NUMBER_OF_THREADS, new NullMonitor());
	}

	public CalcFixedThread(Node fmNode, IMonitor monitor) {
		this(fmNode, NUMBER_OF_THREADS, monitor);
	}

	public CalcFixedThread(Node fmNode, int numberOfSolvers, IMonitor monitor) {
		super(monitor);
		sharedObjects = new SharedObjects(fmNode, numberOfSolvers);
		id = sharedObjects.lastSolverID;
	}

	private CalcFixedThread(CalcFixedThread oldThread) {
		super(oldThread);
		sharedObjects = oldThread.sharedObjects;
		id = ++oldThread.sharedObjects.lastSolverID;
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
		super.start(sharedObjects.numberOfSolvers);
	}

	@Override
	protected boolean beforeWork() {
		return sharedObjects.solver.initSolver(id);
	}

	@Override
	protected void work(String featureName) {
		final Literal curLiteral = new Literal(featureName);
		final byte value = sharedObjects.solver.getValueOf(curLiteral, id);
		switch (value) {
		case 1:
			addLiteral(curLiteral);
			break;
		case -1:
			curLiteral.positive = false;
			addLiteral(curLiteral);
			break;
		default:
			break;
		}
	}

	private synchronized void addLiteral(Literal literal) {
		sharedObjects.fixedLiteralsList.add(literal);
	}

	public List<Literal> getFixedLiterals() {
		return sharedObjects.fixedLiteralsList;
	}

	@Override
	protected CalcFixedThread newThread() {
		return new CalcFixedThread(this);
	}

}
