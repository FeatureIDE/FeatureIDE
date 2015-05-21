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
import org.prop4j.SimpleSatSolver;

import de.ovgu.featureide.fm.core.conf.nodes.Variable;
import de.ovgu.featureide.fm.core.conf.worker.base.AWorkerThread;

/**
 * TODO description
 * 
 * @author Sebastian Krieter
 */
class CalcThread4 extends AWorkerThread<Integer, CalcMasterThread2> implements ISatThread {

	private SimpleSatSolver solver;

	protected CalcThread4(CalcMasterThread2 masterThread) {
		super(masterThread);
		this.solver = new SimpleSatSolver(masterThread.fmNode, 1000);
	}

	private CalcThread4(CalcMasterThread2 masterThread, SimpleSatSolver solver) {
		super(masterThread);
		this.solver = solver;
	}

	public void setKnownLiterals(List<Literal> knownLiterals, Literal l) {
		this.solver.seBackbone(knownLiterals, l);
	}

	@Override
	protected void work(Integer i) {
		final byte value = solver.getValueOf(new Literal(masterThread.featureGraph.featureArray[i]));
		switch (value) {
		case 1:
			masterThread.variableConfiguration.setNewValue(i, Variable.TRUE);
			break;
		case -1:
			masterThread.variableConfiguration.setNewValue(i, Variable.FALSE);
			break;
		default:
			break;
		}
	}

	@Override
	protected CalcThread4 resetWorker() {
		return new CalcThread4(masterThread, solver);
	}

}
