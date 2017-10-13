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
package de.ovgu.featureide.fm.ui.wizards;

import static de.ovgu.featureide.fm.core.localization.StringTable.FILE_NAME_MUST_BE_SPECIFIED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECTED_FILE_ALREADY_EXISTS_;
import static de.ovgu.featureide.fm.core.localization.StringTable.THERE_SHOULD_BE_NO_DOT_IN_THE_FILENAME;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.widgets.Event;
import org.eclipse.ui.dialogs.WizardNewFileCreationPage;

import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;

/**
 * @author Sebastian Krieter
 * @author Marlen Bernier
 * @author Dawid Szczepanski
 * @author Christopher Sontag
 */
public class NewFeatureModelFileLocationPage extends WizardNewFileCreationPage {

	public NewFeatureModelFileLocationPage(String pageName, IStructuredSelection selection) {
		super(pageName, selection);
		setTitle("Choose Location");
		setDescription("Select a path to the new feature model file.");

	}

	public void handleEvent(Event event) {
		checkPathAndFileName(this.getContainerFullPath(), this.getFileName());
	}

	protected void checkPathAndFileName(IPath path, String fileName) {
		if (fileName.isEmpty()) {
			updateStatus(FILE_NAME_MUST_BE_SPECIFIED_);
			return;
		}
		if (fileName.contains(".")) {
			updateStatus(THERE_SHOULD_BE_NO_DOT_IN_THE_FILENAME);
			return;
		}

		if (this.getContainerFullPath() != null) {
			for (IFeatureModelFormat ext : FMFormatManager.getInstance().getExtensions()) {
				IFile file = ResourcesPlugin.getWorkspace().getRoot().getProject(path.segment(0)).getFile(fileName + "." + ext.getSuffix());
				if (file != null && file.exists()) {
					updateStatus(SELECTED_FILE_ALREADY_EXISTS_);
					return;
				}
			}
		}

		updateStatus(null);
	}

	private void updateStatus(String message) {
		setErrorMessage(message);
		setPageComplete(message == null);
	}
}
