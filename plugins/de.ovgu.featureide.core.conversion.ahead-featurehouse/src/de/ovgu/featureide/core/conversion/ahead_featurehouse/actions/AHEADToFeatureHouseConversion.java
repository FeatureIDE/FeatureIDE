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
package de.ovgu.featureide.core.conversion.ahead_featurehouse.actions;

import static de.ovgu.featureide.fm.core.localization.StringTable.CHANGE_COMPOSER_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CHANGE_THE_COMPOSER_OF_PROJECT;
import static de.ovgu.featureide.fm.core.localization.StringTable.FROM_AHEAD_TO_FEATUREHOUSE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.JAK;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.ahead.AheadCorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.featurehouse.FeatureHouseComposer;

/**
 * Changes the composer of an AHEAD project to FeatureHouse.
 *
 * @author Jens Meinicke
 */
public class AHEADToFeatureHouseConversion extends ComposerConversion {

	/**
	 * Changes the composer of the given feature project to <code>FeatureHouse</code>.
	 *
	 * @param featureProject
	 */
	public AHEADToFeatureHouseConversion(final IFeatureProject featureProject) {
		if (featureProject == null) {
			return;
		}
		AheadCorePlugin.getDefault().logInfo(CHANGE_THE_COMPOSER_OF_PROJECT + featureProject.getProjectName() + FROM_AHEAD_TO_FEATUREHOUSE_);
		final Job job = new Job(CHANGE_COMPOSER_) {

			@Override
			protected IStatus run(IProgressMonitor monitor) {
				startProjectConversion(featureProject);
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.BUILD);
		job.schedule();

	}

	/**
	 * Replaces the composer of the given feature project by <code>FeatureHouse</code>.
	 *
	 * @param project
	 */
	@Override
	void changeComposer(IFeatureProject project) {
		project.setComposerID(FeatureHouseComposer.COMPOSER_ID);
	}

	/**
	 * Replaces <code>Super().methodName()</code> by <code>original()</code>.<br> Removes <code>refines</code> from classes that refine.<br> Removes <code>layer
	 * feature;</code> declaration.
	 */
	@Override
	public String changeFile(String fileText, IFile file) {
		fileText = fileText.replaceFirst("layer \\w*;", "");
		fileText = fileText.replaceFirst("refines ", "");
		return fileText.replaceAll("Super\\(\\s*\\w*\\s*\\).\\w*\\(", "original(");
	}

	/**
	 * Replaces the file extension <code>.jak</code> by <code>.java</code> of the given file
	 *
	 * @param file
	 */
	@Override
	void replaceFileExtension(IFile file) {
		try {
			file.move(((IFolder) file.getParent()).getFile(file.getName().replace(JAK, ".java")).getFullPath(), true, null);
		} catch (final CoreException e) {
			AheadCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * @param fileExtension The file extension of a file
	 * @return <code>true</code> if jak
	 */
	@Override
	boolean canConvert(String fileExtension) {
		return "jak".equals(fileExtension);
	}

}
