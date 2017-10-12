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

import static de.ovgu.featureide.fm.core.localization.StringTable.NEW_CONFIGURATION;
import static de.ovgu.featureide.fm.core.localization.StringTable.NEW_FILE_WAS_NOT_ADDED_TO_FILESYSTEM;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;

import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.IConfigurationFormat;
import de.ovgu.featureide.fm.core.io.manager.ConfigFileHandler;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.configuration.ConfigurationEditor;

/**
 * A Wizard to create a new Feature Model file.
 *
 * @author Jens Meinicke
 * @author Marcus Pinnecke
 * @author Marlen Bernier
 * @author Dawid Szczepanski
 */
public class NewConfigurationWizard extends AbstractNewFileWizard<IConfigurationFormat> implements INewWizard {

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".wizard.NewConfigurationWizard";

	private String configFolder;

	public NewConfigurationWizard() {
		setWindowTitle(NEW_CONFIGURATION);
	}

	@Override
	public boolean performFinish() {
		this.initConfigFolder();
		final IConfigurationFormat format = ((NewConfigurationFileFormatPage) formatPage).getFormat();
		final Path configPath = getNewFilePath(format);

		assert (Files.exists(configPath)) : NEW_FILE_WAS_NOT_ADDED_TO_FILESYSTEM;
		String fileName = locationPage.getFileName() + "." + format.getSuffix();

		IFile configFile = ResourcesPlugin.getWorkspace().getRoot().getFile(locationPage.getContainerFullPath().append(configFolder).append(fileName));
		ConfigFileHandler.saveConfig(configPath, new Configuration(defaultFeatureModel()), format);
		
		try {
			// open editor
			FMUIPlugin.getDefault().openEditor(ConfigurationEditor.ID, configFile);
		} catch (final Exception e) {
			FMUIPlugin.getDefault().logError(e);
		}
		return true;
	}

	@Override
	public Path getNewFilePath(IConfigurationFormat format) {
		String fileName = locationPage.getFileName();

		if (!fileName.matches(".+\\." + Pattern.quote(format.getSuffix()))) {
			fileName += "." + format.getSuffix();
			fileName = configFolder + fileName;
		}
		return getFullPath(fileName);
	}

	/**
	 * Initializes the configuration folder, if it exists use the configuration folder otherwise use none
	 * 
	 * @param configFolderName
	 */
	private void initConfigFolder() {
		if (Files.exists(getFullPath("configs"))) {
			configFolder = "configs/";
		} else {
			configFolder = ""; // configuration folder does not exist, use no sub folder
		}
	}

	@Override
	public void init(IWorkbench workbench, IStructuredSelection selection) {
		formatPage = new NewConfigurationFileFormatPage();
		locationPage = new NewConfigurationFileLocationPage("location", selection);
	}
}
