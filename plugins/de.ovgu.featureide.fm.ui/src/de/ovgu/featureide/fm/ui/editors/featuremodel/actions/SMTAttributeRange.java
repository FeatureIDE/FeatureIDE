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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Evaluates the analysis runtime from the open feature model and writes the results into a log.
 *
 * @author Joshua Sprey
 */
public class SMTAttributeRange extends AFeatureModelAction {

	public static final String ID = "de.ovgu.featureide.evaluation";
	IFeatureModelManager featureModelManager;

	public SMTAttributeRange(IFeatureModelManager featureModelManager) {
		super("Evaluate this model", ID, featureModelManager);
		this.featureModelManager = featureModelManager;
		setImageDescriptor(FMUIPlugin.getDefault().getImageDescriptor("icons/wordassist_co.gif"));
	}

	@Override
	public void run() {
		// Also
		final List<IProject> projectList = new LinkedList<IProject>();
		final IWorkspaceRoot workspaceRoot = ResourcesPlugin.getWorkspace().getRoot();
		final IProject[] projects = workspaceRoot.getProjects();
		for (int i = 0; i < projects.length; i++) {
			final IProject project = projects[i];
			if (project.isOpen()) {
				projectList.add(project);
			}
		}

		// Lade modelle
		final List<IFeatureModel> modelleSmall = new ArrayList<>();
		for (final IProject iProject : projects) {
			try {
				for (final IResource resource : iProject.members()) {
					if (resource.getFileExtension().equals("xml")) {
						final Path file = resource.getRawLocation().toFile().toPath();
						final Path absolute = file.toAbsolutePath();
						final FeatureModelManager manager = FeatureModelManager.getInstance(absolute);
						final IFeatureModel model = manager.getObject();
						modelleSmall.add(model);
					}
				}
			} catch (final CoreException e) {
				continue;
			}
		}
	}

}
