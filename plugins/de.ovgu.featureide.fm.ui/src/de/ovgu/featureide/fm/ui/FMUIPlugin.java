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
package de.ovgu.featureide.fm.ui;

import static de.ovgu.featureide.fm.core.localization.StringTable.SELECT_THE_FEATURE_MODEL_FOR_THE_CURRENT_PROJECT;

import java.util.Arrays;
import java.util.Optional;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.dialogs.FilteredResourcesSelectionDialog;
import org.osgi.framework.BundleContext;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.init.LibraryManager;
import de.ovgu.featureide.fm.core.io.ExternalChangeListener;

/**
 * The activator class controls the plug-in life cycle.
 *
 * @author Christian Kaestner
 * @author Thomas Thuem
 */
public class FMUIPlugin extends AbstractUIPlugin {

	public static final String PLUGIN_ID = "de.ovgu.featureide.fm.ui";

	private static FMUIPlugin plugin;

	@Override
	public String getID() {
		return PLUGIN_ID;
	}

	@Override
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
		LibraryManager.registerLibrary(FMUIEclipseLibrary.getInstance());
	}

	@Override
	public void stop(BundleContext context) throws Exception {
		LibraryManager.deregisterLibrary(FMUIEclipseLibrary.getInstance());
		plugin = null;
		super.stop(context);
		final ExternalChangeListener listener = ExternalChangeListener.listener;
		if (listener instanceof IResourceChangeListener) {
			ResourcesPlugin.getWorkspace().removeResourceChangeListener((IResourceChangeListener) listener);
		}
	}

	public static FMUIPlugin getDefault() {
		return plugin;
	}

	public static Image getImage(String name) {
		return getDefault().getImageDescriptor("icons/" + name).createImage();
	}

	/**
	 * Opens a Dialog to select the file of the {@link IFeatureModel}
	 *
	 * @return a string describing the absolute path of the selected model file
	 * @see FileDialog#open()
	 */
	public static IFile openFileDialog(IProject project) {
		if ((project != null) && (project.getLocation() != null)) {
			final FilteredResourcesSelectionDialog dialog = new FilteredResourcesSelectionDialog(getShell(), false, project, IResource.FILE);
			dialog.setTitle(SELECT_THE_FEATURE_MODEL_FOR_THE_CURRENT_PROJECT);
			dialog.setMessage(SELECT_THE_FEATURE_MODEL_FOR_THE_CURRENT_PROJECT);
			dialog.setInitialPattern("?");
			if (dialog.open() == FilteredResourcesSelectionDialog.OK) {
				final Object[] results = dialog.getResult();
				if ((results != null) && (results.length > 0)) {
					final Object result = results[0];
					if (FMCorePlugin.isFeatureModelFile(result)) {
						final IFile file = (IFile) result;
						FMCorePlugin.setPersitentModelFilePath(project.getProject(), file.getLocation().toOSString());
						return file;
					}
				}
			}
		}
		return null;
	}

	public static Shell getShell() {
		IWorkbenchWindow activeWorkbenchWindow = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		if (activeWorkbenchWindow == null) {
			activeWorkbenchWindow = Arrays.stream(PlatformUI.getWorkbench().getWorkbenchWindows()).findFirst().orElse(null);
		}
		return Optional //
				.ofNullable(activeWorkbenchWindow) //
				.map(IWorkbenchWindow::getShell) //
				.orElse(null);
	}

	public static Optional<IFile> findModelFile(IProject project) {
		IFile modelFile = FMCorePlugin.findModelFile(project).orElse(null);
		if (modelFile == null) {
			modelFile = openFileDialog(project.getProject());
			if (modelFile == null) {
				return Optional.empty();
			}
		}
		return Optional.of(modelFile);
	}

}
