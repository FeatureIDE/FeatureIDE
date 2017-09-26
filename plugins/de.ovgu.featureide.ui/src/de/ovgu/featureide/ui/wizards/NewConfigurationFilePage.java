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

import static de.ovgu.featureide.fm.core.localization.StringTable.ALREADY_EXISTS_;
import static de.ovgu.featureide.fm.core.localization.StringTable.ENTER_THE_NAME_OF_THE_CONFIGURATION_FILE__IT_WILL_BE_PLACED_IN_THE_CONFIGURATIONS_DIRECTORY_OF_THE;
import static de.ovgu.featureide.fm.core.localization.StringTable.FILE;
import static de.ovgu.featureide.fm.core.localization.StringTable.FILE_NAME_MUST_BE_SPECIFIED;
import static de.ovgu.featureide.fm.core.localization.StringTable.FILE_NAME_MUST_BE_VALID;
import static de.ovgu.featureide.fm.core.localization.StringTable.NEW_CONFIGURATION;
import static de.ovgu.featureide.fm.core.localization.StringTable.NO_PROJECT_SELECTED;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECTED_FEATUREIDE_PROJECT;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECTED_PROJECT_IS_NOT_A_FEATUREIDE_PROJECT;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.dialogs.IDialogPage;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.configuration.XMLConfFormat;
import de.ovgu.featureide.fm.core.io.IConfigurationFormat;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * The NEW wizard page allows setting the container for the new file as well as the file name. The page will only accept file name without the extension OR with
 * the extension that matches the expected one (.config).
 *
 * @author Christian Becker
 * @author Jens Meinicke
 */
public class NewConfigurationFilePage extends WizardPage {

	private final List<IConfigurationFormat> formatExtensions = ConfigFormatManager.getInstance().getExtensions();

	private Combo featureComboProject;
	private Combo formatCombo;

	private Text fileText;

	private IFolder configFolder;

	private IFeatureProject featureProject = null;

	private final Collection<IFeatureProject> featureProjects = CorePlugin.getFeatureProjects();

	private String text;

	private List<String> configNames = new LinkedList<>();
	private boolean projectbool = false;
	private boolean configbool = false;

	/**
	 * Constructor for SampleNewWizardPage.
	 *
	 * @param pageName
	 */
	public NewConfigurationFilePage(IFolder configFolder) {
		super("wizardPage");
		setTitle(NEW_CONFIGURATION);
		setDescription(ENTER_THE_NAME_OF_THE_CONFIGURATION_FILE__IT_WILL_BE_PLACED_IN_THE_CONFIGURATIONS_DIRECTORY_OF_THE + SELECTED_FEATUREIDE_PROJECT);
		this.configFolder = configFolder;
	}

	/**
	 * @see IDialogPage#createControl(Composite)
	 */
	@Override
	public void createControl(Composite parent) {
		final GridData gd = new GridData(GridData.FILL_HORIZONTAL);
		final Composite composite = new Composite(parent, SWT.NULL);
		final GridLayout layout = new GridLayout();
		layout.numColumns = 3;
		layout.verticalSpacing = 9;
		composite.setLayout(layout);

		Label label = new Label(composite, SWT.NULL);
		label.setText("&Project:");
		featureComboProject = new Combo(composite, SWT.BORDER | SWT.SINGLE);
		featureComboProject.setLayoutData(gd);
		new Label(composite, SWT.NULL);

		label = new Label(composite, SWT.NULL);
		label.setText("&File name:");
		fileText = new Text(composite, SWT.BORDER | SWT.SINGLE);
		fileText.setLayoutData(gd);
		new Label(composite, SWT.NULL);

		label = new Label(composite, SWT.NULL);
		label.setText("&Format:");
		formatCombo = new Combo(composite, SWT.BORDER | SWT.SINGLE);
		formatCombo.setLayoutData(gd);
		new Label(composite, SWT.NULL);

		initialize();
		addListeners();
		dialogChanged();
		setControl(composite);
		projectbool = true;
	}

	/**
	 * Tests if the current workbench selection is a suitable container to use.
	 */
	private void addListeners() {
		featureComboProject.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				featureProject = null;
				text = featureComboProject.getText();
				for (final IFeatureProject feature : featureProjects) {
					if (text.equalsIgnoreCase(feature.getProjectName())) {
						featureProject = feature;
					}
				}
				if (featureProject != null) {
					try {
						for (final IResource configFile : featureProject.getConfigFolder().members()) {
							if (configFile instanceof IFile) {
								configNames.add(configFile.getName());// .split("[.]")[0]);
							}
						}
					} catch (final CoreException e2) {
						UIPlugin.getDefault().logError(e2);
					}
					final IResource res = ResourcesPlugin.getWorkspace().getRoot().findMember(featureProject.getProjectName());
					final IFeatureProject data = CorePlugin.getFeatureProject(res);
					if (data != null) {
						configFolder = data.getConfigFolder();
					}
				}
				dialogChanged();
			}
		});
		fileText.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				dialogChanged();
			}
		});
		formatCombo.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				dialogChanged();
			}
		});
	}

	private void initialize() {
		for (final IFeatureProject feature : featureProjects) {
			featureComboProject.add(feature.getProjectName());
		}
		if (configFolder != null) {
			featureComboProject.setText(configFolder.getProject().getName());
		}
		for (final IConfigurationFormat format : formatExtensions) {
			formatCombo.add(format.getName() + " (*." + format.getSuffix() + ")");
		}
		try {
			formatCombo.select(formatExtensions.indexOf(ConfigFormatManager.getInstance().getExtension(XMLConfFormat.ID)));
		} catch (final NoSuchExtensionException e) {
			formatCombo.select(0);
		}
	}

	private void dialogChanged() {
		final String fileName = getFileName();
		if ((featureComboProject.getText().length() == 0) && !projectbool) {
			setErrorMessage(null);
			setPageComplete(false);
			projectbool = true;
			return;
		}

		if (featureComboProject.getText().length() == 0) {
			updateStatus(NO_PROJECT_SELECTED);
			return;
		}

		if (!isFeatureProject(featureComboProject.getText())) {
			updateStatus(SELECTED_PROJECT_IS_NOT_A_FEATUREIDE_PROJECT);
			return;
		}

		if (fileName.length() != 0) {
			configbool = true;
			final String fullFileName = fileName + "." + featureProject.getComposer().getConfigurationExtension();
			if (featureProject.getConfigFolder().getFile(fullFileName).exists()) {
				updateStatus(FILE + fullFileName + ALREADY_EXISTS_);
				return;
			}
		} else if (configbool) {
			updateStatus(FILE_NAME_MUST_BE_SPECIFIED);
			return;
		} else {
			setErrorMessage(null);
			setPageComplete(false);
			return;
		}
		if (fileName.replace('\\', '/').indexOf('/', 1) > 0) {
			updateStatus(FILE_NAME_MUST_BE_VALID);
			return;
		}

		final int dotLoc = fileName.lastIndexOf('.');
		if (dotLoc != -1) {
			updateStatus("Configuration name must not contain \".\"");
			return;
		}
		updateStatus(null);
	}

	private void updateStatus(String message) {
		setErrorMessage(message);
		setPageComplete(message == null);
	}

	public IFolder getContainerObject() {
		return configFolder;
	}

	public String getFileName() {
		return fileText.getText();
	}

	public IConfigurationFormat getFormat() {
		return formatExtensions.get(formatCombo.getSelectionIndex());
	}

	public boolean isFeatureProject(String text) {
		boolean isFP = false;
		for (final IFeatureProject feature : featureProjects) {
			if (text.equalsIgnoreCase(feature.getProjectName())) {
				isFP = true;
				featureProject = feature;
				try {
					configNames = new LinkedList<String>();
					for (final IResource configurationFile : featureProject.getConfigFolder().members()) {
						if (configurationFile instanceof IFile) {
							configNames.add(configurationFile.getName().split("[.]")[0]);
						}
					}
				} catch (final CoreException e2) {
					UIPlugin.getDefault().logError(e2);
				}
			}
		}
		return isFP;
	}

	public IFeatureProject getFeatureProject() {
		return featureProject;
	}
}
