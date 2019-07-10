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
package de.ovgu.featureide.fm.core.analysis.cnf.manipulator;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds atomic sets.
 *
 * @author Sebastian Krieter
 */
public abstract class AbstractManipulator implements LongRunningMethod<CNF> {

	protected final CNF orgCNF;

	public AbstractManipulator(CNF orgCNF) {
		this.orgCNF = orgCNF;
	}

	@Override
	public final CNF execute(IMonitor monitor) throws Exception {
		if (orgCNF == null) {
			return null;
		}
		monitor.checkCancel();
		try {
			return manipulate(monitor);
		} catch (final Throwable e) {
			throw e;
		}
	}

	protected abstract CNF manipulate(IMonitor monitor) throws Exception;

}
