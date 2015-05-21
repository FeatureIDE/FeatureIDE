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

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.conf.FeatureGraph;
import de.ovgu.featureide.fm.core.conf.IConfigurationChanger;
import de.ovgu.featureide.fm.core.conf.worker.base.IMasterThread;
import de.ovgu.featureide.fm.core.conf.worker.base.InternWorkerThread;

public class CalcMasterThread2 implements IMasterThread<Integer> {

	final FeatureGraph featureGraph;
	final IConfigurationChanger variableConfiguration;
	final Node fmNode;

	private final int mode;

	public CalcMasterThread2(FeatureGraph featureGraph, IConfigurationChanger variableConfiguration, Node fmNode, int mode) {
		this.featureGraph = featureGraph;
		this.variableConfiguration = variableConfiguration;
		this.fmNode = fmNode;
		this.mode = mode;
	}

	@Override
	public InternWorkerThread<Integer> newWorker() {
		switch (mode) {
		case 2:
			return new CalcThread2(this);
		case 3:
			return new CalcThread3(this);
		case 4:
			return new CalcThread4(this);
		default:
			return new CalcThread2(this);
		}
	}

}
