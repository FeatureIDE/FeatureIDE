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
package de.ovgu.featureide.ui.android.wizards;

import static de.ovgu.featureide.fm.core.localization.StringTable.ADD_THE_FEATUREIDE_NATURE_TO_ANDROID_PROJECTS_;
import static de.ovgu.featureide.fm.core.localization.StringTable.BUILD;
import static de.ovgu.featureide.fm.core.localization.StringTable.BUILD_PATH_EQUALS_CONFIGURATIONS_PATH_;
import static de.ovgu.featureide.fm.core.localization.StringTable.EQUATIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.NO_COMPOSITION_ENGINES_INSTALLED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.PLEASE_SELECT_A_COMPOSER_FROM_THE_SELECTION_BELOW_;
import static de.ovgu.featureide.fm.core.localization.StringTable.SETS_THE_PATH_OF_COMPOSED_FILES_;
import static de.ovgu.featureide.fm.core.localization.StringTable.SETS_THE_PATH_OF_CONFIGURATIONFILES_;
import static de.ovgu.featureide.fm.core.localization.StringTable.SETS_THE_PATH_OF_SOURCE_FILES_;
import static de.ovgu.featureide.fm.core.localization.StringTable.SOURCE;
import static de.ovgu.featureide.fm.core.localization.StringTable.SOURCE_PATH_EQUALS_BUILD_PATH_;
import static de.ovgu.featureide.fm.core.localization.StringTable.SOURCE_PATH_EQUALS_CONFIGURATIONS_PATH_;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_ANDROID_RESOURCE_FILE_PATH_CANNOT_BE_CHANGED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_ANDROID_SOURCE_FILE_PATH_CANNOT_BE_CHANGED_;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.core.builder.ComposerExtensionManager;
import de.ovgu.featureide.core.builder.IComposerExtension;
import de.ovgu.featureide.core.builder.IComposerExtensionBase;
import de.ovgu.featureide.ui.wizards.NewFeatureProjectPage;

/**
 * Dialog page to add the featureIDE nature to an existing Android project.
 *
 * @author Lars-Christian Schulz
 * @author Eric Guimatsia
 */
public class ConversionPage extends NewFeatureProjectPage {

	public ConversionPage() {
		super();
		setDescription(ADD_THE_FEATUREIDE_NATURE_TO_ANDROID_PROJECTS_);
	}

	@Override
	public void createControl(Composite parent) {
		final Composite container = new Composite(parent, SWT.NULL);
		final GridLayout gridLayout = new GridLayout();
		gridLayout.numColumns = 1;
		container.setLayout(gridLayout);
		setControl(container);

		final Group toolGroup = new Group(container, SWT.NONE);
		toolGroup.setText("Composer Selection:");
		toolGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		final GridLayout projGridLayout = new GridLayout();
		projGridLayout.numColumns = 2;
		toolGroup.setLayout(projGridLayout);

		final Label helloLabel = new Label(toolGroup, SWT.NONE);
		final GridData gridData = new GridData(GridData.FILL_BOTH);
		gridData.horizontalSpan = 2;
		helloLabel.setLayoutData(gridData);
		helloLabel.setText(PLEASE_SELECT_A_COMPOSER_FROM_THE_SELECTION_BELOW_);

		Label label = new Label(toolGroup, SWT.NONE);
		label.setText("Composers:");
		toolCB = new Combo(toolGroup, SWT.READ_ONLY | SWT.DROP_DOWN);
		toolCB.setLayoutData(new GridData(GridData.FILL_BOTH));

		final Label descriptionLabel = new Label(toolGroup, SWT.NONE);
		final GridData gridData2 = new GridData(GridData.FILL_BOTH);
		gridData2.horizontalSpan = 2;
		descriptionLabel.setLayoutData(gridData2);

		final StringBuilder descriptionStringBuilder = new StringBuilder();
		descriptionStringBuilder.append("Possible choices are:\n\n");
		final List<IComposerExtension> composerExtensions = ComposerExtensionManager.getInstance().getComposers();

		// Filter for Android compatible composers
		final List<IComposerExtension> androidCompatibleComposers = new ArrayList<IComposerExtension>();
		for (final IComposerExtension composer : composerExtensions) {
			if (composer.supportsAndroid()) {
				androidCompatibleComposers.add(composer);
			}
		}

		extensions = new IComposerExtensionBase[androidCompatibleComposers.size()];
		androidCompatibleComposers.toArray(extensions);
		Arrays.sort(extensions, new Comparator<IComposerExtensionBase>() {

			@Override
			public int compare(IComposerExtensionBase arg0, IComposerExtensionBase arg1) {
				return arg0.getName().compareTo(arg1.getName());
			}
		});

		for (final IComposerExtensionBase composerExtension : extensions) {
			descriptionStringBuilder.append(composerExtension.getName());
			descriptionStringBuilder.append(": ");
			descriptionStringBuilder.append(composerExtension.getDescription());
			descriptionStringBuilder.append("\n");
			toolCB.add(composerExtension.getName());
		}

		String descriptionString = descriptionStringBuilder.toString();
		if (composerExtensions.isEmpty()) {
			descriptionString = NO_COMPOSITION_ENGINES_INSTALLED_;
			setDescription(descriptionString);
			toolCB.setEnabled(false);
		}
		descriptionLabel.setText(descriptionString);
		toolCB.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				composerExtension = extensions[toolCB.getSelectionIndex()];
			}
		});
		toolCB.select(0);

		// Path Group
		pathGroup = new Group(container, SWT.NONE);
		layout.numColumns = 2;
		layout.verticalSpacing = 9;
		pathGroup.setText("Path Specification:");
		pathGroup.setLayoutData(gd);
		pathGroup.setLayout(layout);

		String tooltip = THE_ANDROID_SOURCE_FILE_PATH_CANNOT_BE_CHANGED_;
		label = new Label(pathGroup, SWT.NULL);
		label.setText("Android Source Path:");
		label.setToolTipText(tooltip);
		final Text androidSrcPath = new Text(pathGroup, SWT.BORDER | SWT.SINGLE | SWT.READ_ONLY);
		androidSrcPath.setLayoutData(gd);
		androidSrcPath.setText("src");
		androidSrcPath.setToolTipText(tooltip);

		tooltip = THE_ANDROID_RESOURCE_FILE_PATH_CANNOT_BE_CHANGED_;
		label = new Label(pathGroup, SWT.NULL);
		label.setText("Android Resource Files Path:");
		label.setToolTipText(tooltip);
		final Text androidResPath = new Text(pathGroup, SWT.BORDER | SWT.SINGLE | SWT.READ_ONLY);
		androidResPath.setLayoutData(gd);
		androidResPath.setText("res");
		androidResPath.setToolTipText(tooltip);

		tooltip = SETS_THE_PATH_OF_COMPOSED_FILES_;
		buildLabel = new Label(pathGroup, SWT.NULL);
		buildLabel.setText("&Composed files Path:");
		buildLabel.setToolTipText(tooltip);
		buildPath = new Text(pathGroup, SWT.BORDER | SWT.SINGLE);
		buildPath.setLayoutData(gd);
		buildPath.setText("composed");
		buildPath.setToolTipText(tooltip);

		tooltip = SETS_THE_PATH_OF_SOURCE_FILES_;
		label = new Label(pathGroup, SWT.NULL);
		label.setText("&Source Path:");
		label.setToolTipText(tooltip);
		sourcePath = new Text(pathGroup, SWT.BORDER | SWT.SINGLE);
		sourcePath.setLayoutData(gd);
		sourcePath.setText("source");
		sourcePath.setToolTipText(tooltip);

		tooltip = SETS_THE_PATH_OF_CONFIGURATIONFILES_;
		label = new Label(pathGroup, SWT.NULL);
		label.setText("&Configurations Path:");
		label.setToolTipText(tooltip);
		configsPath = new Text(pathGroup, SWT.BORDER | SWT.SINGLE);
		configsPath.setLayoutData(gd);
		configsPath.setText("configs");
		configsPath.setToolTipText(tooltip);

		addListeners();
	}

	@Override
	protected void dialogChanged() {
		final IComposerExtensionBase compositionTool = getCompositionTool();
		sourcePath.setEnabled(compositionTool.hasFeatureFolder());
		buildPath.setEnabled(compositionTool.hasSourceFolder());

		if (getSourcePath().equals("src") || getSourcePath().equals("res")) {
			updateStatus("Source path cannot be \"/src\" or \"/res\".");
			return;
		}
		if (getBuildPath().equals("src") || getBuildPath().equals("res")) {
			updateStatus("Build path cannot be \"/src\" or \"/res\".");
			return;
		}
		if (getConfigPath().equals("src") || getConfigPath().equals("res")) {
			updateStatus("Config path cannot be \"/src\" or \"/res\".");
			return;
		}
		if (getSourcePath().equals(getConfigPath())) {
			updateStatus(SOURCE_PATH_EQUALS_CONFIGURATIONS_PATH_);
			return;
		}
		if (getSourcePath().equals(getBuildPath())) {
			updateStatus(SOURCE_PATH_EQUALS_BUILD_PATH_);
			return;
		}
		if (getBuildPath().equals(getConfigPath())) {
			updateStatus(BUILD_PATH_EQUALS_CONFIGURATIONS_PATH_);
			return;
		}
		if (isPathEmpty(getSourcePath(), SOURCE) || isPathEmpty(getBuildPath(), BUILD) || isPathEmpty(getConfigPath(), EQUATIONS)
			|| isInvalidPath(getSourcePath(), SOURCE) || isInvalidPath(getBuildPath(), BUILD) || isInvalidPath(getConfigPath(), EQUATIONS)) {
			return;
		}

		updateStatus(null);
	}
}
