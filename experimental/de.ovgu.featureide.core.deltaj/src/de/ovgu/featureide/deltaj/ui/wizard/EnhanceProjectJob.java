/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.deltaj.ui.wizard;

import java.io.FileNotFoundException;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.core.CorePlugin;

/**
 * A Job to allow project enhancement by the DeltaJNewProjectWizardExtension.
 * @author Sven Schuster
 */
public class EnhanceProjectJob extends Job {
	private DeltaJNewProjectWizardExtension ext;

	/**
	 * @param name
	 * @param ext the DeltaJNewProjectWizardExtension
	 */
	public EnhanceProjectJob(String name, DeltaJNewProjectWizardExtension ext) {
		super(name);
		this.ext = ext;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.runtime.jobs.Job#run(org.eclipse.core.runtime.IProgressMonitor)
	 */
	@Override
	protected IStatus run(IProgressMonitor monitor) {
		try {
			if(ext.getModel() != null) {
				ext.createDeltas();
				ext.replaceModel();
			}
			return Status.OK_STATUS;
		} catch(FileNotFoundException e) {
			CorePlugin.getDefault().logError(e);
			return Status.CANCEL_STATUS;
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
			return Status.CANCEL_STATUS;
		}
	}
}
