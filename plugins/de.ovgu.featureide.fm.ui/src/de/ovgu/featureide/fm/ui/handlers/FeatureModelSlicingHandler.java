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
package de.ovgu.featureide.fm.ui.handlers;

import java.nio.file.Paths;
import java.util.Collection;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Display;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.SliceFeatureModelJob;
import de.ovgu.featureide.fm.core.job.util.JobArguments;
import de.ovgu.featureide.fm.ui.handlers.base.AFileHandler;
import de.ovgu.featureide.fm.ui.wizards.AbstractWizard;
import de.ovgu.featureide.fm.ui.wizards.FeatureModelSlicingWizard;
import de.ovgu.featureide.fm.ui.wizards.WizardConstants;

public class FeatureModelSlicingHandler extends AFileHandler {

	@SuppressWarnings("unchecked")
	@Override
	protected void singleAction(IFile file) {
		final IFeatureModel featureModel = FeatureModelManager.load(Paths.get(file.getLocationURI())).getObject();
		if (featureModel != null) {
			final AbstractWizard wizard = new FeatureModelSlicingWizard("Feature-Model Slicing");
			wizard.putData(WizardConstants.KEY_IN_FEATUREMODEL, featureModel);
			if (Window.OK == new WizardDialog(Display.getCurrent().getActiveShell(), wizard).open()) {
				final JobArguments arguments = new SliceFeatureModelJob.Arguments(Paths.get(file.getLocationURI()), featureModel,
						(Collection<String>) wizard.getData(WizardConstants.KEY_OUT_FEATURES), true);
				LongRunningWrapper.getRunner(arguments.createJob()).schedule();
			}
		}

	}

}
