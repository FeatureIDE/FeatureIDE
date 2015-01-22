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
package de.ovgu.featureide.featurehouse.ui.actions;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IActionDelegate;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.featurehouse.FeatureHouseCorePlugin;
import de.ovgu.featureide.featurehouse.meta.FeatureStubsGenerator;

public class GenerateFeatureStubsAction implements IActionDelegate {
	private IFeatureProject featureProject = null;

	@Override
	public void run(IAction action) {
		FeatureStubsGenerator fsg = new FeatureStubsGenerator(featureProject);
		if (fsg.generate()) {
			FeatureHouseCorePlugin.getDefault().logInfo("Feature Stubs Generation started.");
		}

	}

	@Override
	public void selectionChanged(IAction action, ISelection selection) {
		Object first = ((IStructuredSelection) selection).getFirstElement();
		if (first instanceof IProject) {
			IProject project = (IProject) first;
			IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
			if (featureProject != null) {
				this.featureProject = featureProject;
				return;
			}
		}
	}
}
