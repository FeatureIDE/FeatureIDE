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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.job.monitor;

import de.ovgu.featureide.fm.core.functional.Functional.IConsumer;
import de.ovgu.featureide.fm.core.job.IJob;

/**
 * Control object for {@link IJob}s. Can be used to check for cancel request, display job progress, and calling intermediate functions.
 *
 * @author Sebastian Krieter
 */
public abstract class AMonitor implements IMonitor {

	protected final AMonitor parent;

	protected IConsumer<Object> intermediateFunction = null;

	public AMonitor(AMonitor parent) {
		this.parent = parent;
	}

	public AMonitor() {
		parent = null;
	}

	@Override
	public final void invoke(Object t) {
		if (intermediateFunction != null) {
			intermediateFunction.invoke(t);
		}
	}

	@Override
	public final void step() throws MethodCancelException {
		step(null);
	}

	@Override
	public final void step(Object t) throws MethodCancelException {
		worked();
		invoke(t);
		checkCancel();
	}

	@Override
	public final void setIntermediateFunction(IConsumer<Object> intermediateFunction) {
		this.intermediateFunction = intermediateFunction;
	}

}
