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
package de.ovgu.featureide.ui.wizards;

import static de.ovgu.featureide.fm.core.localization.StringTable.ADDS_THE_FEATUREIDE_NATURE_TO_THE_PROJECT;
import static de.ovgu.featureide.fm.core.localization.StringTable.RESTRICTION;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_BUILD_PATH_IS_SET_TO_THE_JAVA_PROJECTS_SOURCE_PATH_AUTOMATICALLY;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.internal.core.JavaProject;
import org.eclipse.swt.widgets.Composite;

import de.ovgu.featureide.ui.UIPlugin;

/**
 * A dialog page for adding a FeatureC Project
 *
 * @author Christopher Kruczek
 * @author Andy Kenner
 */
@SuppressWarnings(RESTRICTION)
public class FeatureCProjectPage extends NewFeatureProjectPage {

	private final IProject project;
	private static final String JAVA_NATURE = "org.eclipse.jdt.core.javanature";
	private static final String MESSAGE = THE_BUILD_PATH_IS_SET_TO_THE_JAVA_PROJECTS_SOURCE_PATH_AUTOMATICALLY;

	public FeatureCProjectPage(IProject project) {
		super();
		setDescription(ADDS_THE_FEATUREIDE_NATURE_TO_THE_PROJECT + project.getName() + ".");
		this.project = project;
	}

	@Override
	public void createControl(Composite parent) {
		super.createControl(parent);
		setBuildPath();
	}

	/**
	 * Set the build path to the java projects build path
	 */
	private void setBuildPath() {
		try {
			if (project.hasNature(JAVA_NATURE)) {
				final JavaProject javaProject = new JavaProject(project, null);
				for (final IClasspathEntry entry : javaProject.getRawClasspath()) {
					if (entry.getEntryKind() == IClasspathEntry.CPE_SOURCE) {
						String path = entry.getPath().toOSString();
						final String fileSeparator = System.getProperty("file.separator");

						if (path.contains(fileSeparator)) {
							path = path.substring(path.indexOf(fileSeparator) + 1);
						}
						if (path.contains(fileSeparator)) {
							path = path.substring(path.indexOf(fileSeparator) + 1);
						}

						buildPath.setText(path);
						buildPath.setEnabled(false);
						buildLabel.setToolTipText(MESSAGE);
						return;
					}
				}
			}
		} catch (final CoreException e) {
			UIPlugin.getDefault().logError(e);
		}
	}
}
