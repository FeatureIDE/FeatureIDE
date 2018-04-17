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
package de.ovgu.featureide.fm.ui.handlers.base;

import java.util.LinkedList;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Display;

import de.ovgu.featureide.fm.ui.wizards.AbstractWizard;

/**
 *
 * @author Sebastian Krieter
 */
public abstract class AProjectJobHandler extends ASelectionHandler {

	protected final LinkedList<IProject> projects = new LinkedList<IProject>();

	protected AbstractWizard wizard;

	@Override
	protected boolean startAction(IStructuredSelection selection) {
		wizard = instantiateWizard();
		if (Window.OK == new WizardDialog(Display.getCurrent().getActiveShell(), wizard).open()) {
			final SelectionWrapper<IProject> selectionWrapper = SelectionWrapper.init(selection, IProject.class);
			projects.clear();
			for (IProject curProject; (curProject = selectionWrapper.getNext()) != null;) {
				projects.add(curProject);
			}
			return true;
		}
		return false;
	}

	@Override
	protected void singleAction(Object element) {}

	protected abstract AbstractWizard instantiateWizard();

	@Override
	protected abstract void endAction();

}
