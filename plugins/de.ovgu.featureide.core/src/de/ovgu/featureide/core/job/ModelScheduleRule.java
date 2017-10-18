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
package de.ovgu.featureide.core.job;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.jobs.ISchedulingRule;

/**
 * This simple rule is used to prevent a concurrent write and read access of different jobs. In our case, we use the rule to prevent a read access to the model
 * file while the model file is written.
 *
 * @author Reimar Schroeter
 */
public class ModelScheduleRule implements ISchedulingRule {

	public static ModelScheduleRule RULE = new ModelScheduleRule();

	@Override
	public boolean isConflicting(ISchedulingRule rule) {
		if ((rule instanceof IProject) || (rule instanceof IFolder)) {
			return true;
		}
		return rule == this;
	}

	@Override
	public boolean contains(ISchedulingRule rule) {
		if ((rule instanceof IProject) || (rule instanceof IFolder)) {
			return true;
		}
		return rule == this;
	}

}
