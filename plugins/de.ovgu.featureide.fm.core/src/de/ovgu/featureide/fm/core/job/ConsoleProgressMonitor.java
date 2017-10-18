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
package de.ovgu.featureide.fm.core.job;

import org.eclipse.core.runtime.NullProgressMonitor;

/**
 * Prints the current work amount to the console.
 *
 * @author Sebastian Krieter
 */
public class ConsoleProgressMonitor extends NullProgressMonitor {

	private int worked;

	@Override
	public void beginTask(String name, int totalWork) {
		super.beginTask(name, totalWork);
		worked = totalWork;
		System.out.println(worked);
	}

	@Override
	public void worked(int work) {
		super.worked(work);
		if (work > 0) {
			worked -= work;
			synchronized (System.out) {
				System.out.println(worked);
			}
		}
	}

}
