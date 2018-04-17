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
package de.ovgu.featureide.core.featuremodeling;

import java.nio.file.Paths;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.DefaultFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;

/**
 *
 * ComposerExtensionClass for the Feature Modeling extension.
 *
 * @author Jens Meinicke
 */
public class FeatureModeling extends ComposerExtensionClass {

	@Override
	public void performFullBuild(IFile config) {

	}

	@Override
	public void addCompiler(IProject project, String sourcePath, String configPath, String buildPath) {

	}

	@Override
	public boolean hasFeatureFolder() {
		return false;
	}

	@Override
	public boolean hasSourceFolder() {
		return false;
	}

	@Override
	public boolean hasBuildFolder() {
		return false;
	}

	@Override
	public boolean hasSource() {
		return false;
	}

	@Override
	public boolean clean() {
		return false;
	}

	@Override
	public void copyNotComposedFiles(Configuration config, IFolder destination) {

	}

	@Override
	public Mechanism getGenerationMechanism() {
		return null;
	}

	@Override
	public void buildConfiguration(IFolder folder, Configuration configuration, String congurationName) {
		try {
			final IContainer parent = folder.getParent();
			if (!parent.exists()) {
				folder.create(true, true, null);
			}
			final IPersistentFormat<Configuration> format = ConfigFormatManager.getInstance().getFormatById(DefaultFormat.ID);
			final IFile configurationFile = parent.getFile(new Path(congurationName + "." + format.getSuffix()));
			SimpleFileHandler.save(Paths.get(configurationFile.getLocationURI()), configuration, format);
			copyNotComposedFiles(configuration, folder);
		} catch (CoreException | NoSuchExtensionException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	@Override
	public boolean supportsMigration() {
		return false;
	}

	@Override
	public boolean createFolderForFeatures() {
		return false;
	}

	@Override
	public void postCompile(IResourceDelta delta, IFile buildFile) {

	}

	@Override
	public boolean showContextFieldsAndMethods() {
		return false;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.IComposerExtensionBase#hasPropertyManager()
	 */
	@Override
	public boolean hasPropertyManager() {
		// TODO Auto-generated method stub
		return false;
	}
}
