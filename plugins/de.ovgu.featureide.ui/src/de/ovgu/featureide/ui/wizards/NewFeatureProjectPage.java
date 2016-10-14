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
package de.ovgu.featureide.ui.wizards;

import static de.ovgu.featureide.fm.core.localization.StringTable.BUILD;
import static de.ovgu.featureide.fm.core.localization.StringTable.BUILD_PATH_EQUALS_CONFIGURATIONS_PATH_;
import static de.ovgu.featureide.fm.core.localization.StringTable.BUILD_PATH_RESTRICTION_ANDROID;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONFIG_PATH_RESTRICTION_ANDROID;
import static de.ovgu.featureide.fm.core.localization.StringTable.CREATES_A_FEATUREIDE_PROJECT;
import static de.ovgu.featureide.fm.core.localization.StringTable.EQUATIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.NO_COMPOSITION_ENGINES_INSTALLED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.PATH_MUST_BE_SPECIFIED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.PATH_MUST_BE_VALID;
import static de.ovgu.featureide.fm.core.localization.StringTable.PLEASE_SELECT_A_COMPOSER_FROM_THE_SELECTION_BELOW_;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECT_A_COMPOSER;
import static de.ovgu.featureide.fm.core.localization.StringTable.SETS_THE_PATH_OF_COMPOSED_FILES_;
import static de.ovgu.featureide.fm.core.localization.StringTable.SETS_THE_PATH_OF_CONFIGURATIONFILES_;
import static de.ovgu.featureide.fm.core.localization.StringTable.SETS_THE_PATH_OF_FEATUREFOLDERS_;
import static de.ovgu.featureide.fm.core.localization.StringTable.SOURCE;
import static de.ovgu.featureide.fm.core.localization.StringTable.SOURCE_PATH_EQUALS_BUILD_PATH_;
import static de.ovgu.featureide.fm.core.localization.StringTable.SOURCE_PATH_EQUALS_CONFIGURATIONS_PATH_;
import static de.ovgu.featureide.fm.core.localization.StringTable.SOURCE_PATH_RESTRICTION_ANDROID;

import java.util.Arrays;
import java.util.Comparator;
import java.util.List;

import org.eclipse.jface.wizard.WizardPage;
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

/**
 * A dialog page for creating FeatureIDE projects.
 * 
 * @author Marcus Leich
 */
public class NewFeatureProjectPage extends WizardPage {

	protected IComposerExtensionBase composerExtension = null;
	protected IComposerExtensionBase[] extensions = null;
	
	protected Text sourcePath;
	protected Text configsPath;
	protected Text buildPath;
	
	protected Combo toolCB;
	protected GridData gd = new GridData(GridData.FILL_HORIZONTAL);
	protected GridLayout layout = new GridLayout();
	protected Group pathGroup;
	protected Label buildLabel;
	private boolean canFlipToNextPage = true;
	
	protected NewFeatureProjectPage() {
		super("");
		setTitle(SELECT_A_COMPOSER);
		setDescription(CREATES_A_FEATUREIDE_PROJECT);
	}
	
	public void createControl(Composite parent) {
		Composite container = new Composite(parent, SWT.NULL);
	    final GridLayout gridLayout = new GridLayout();
	    gridLayout.numColumns = 1;
	    container.setLayout(gridLayout);
	    setControl(container);
	    
	    Group toolGroup = new Group(container, SWT.NONE);
		toolGroup.setText("Composer Selection:");
		toolGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		GridLayout projGridLayout = new GridLayout();
		projGridLayout.numColumns = 2;
		toolGroup.setLayout(projGridLayout);
		
		final Label helloLabel = new Label(toolGroup, SWT.NONE);
		GridData gridData = new GridData(GridData.FILL_BOTH);
		gridData.horizontalSpan = 2;
		helloLabel.setLayoutData(gridData);
		helloLabel.setText(PLEASE_SELECT_A_COMPOSER_FROM_THE_SELECTION_BELOW_);
		
	    Label label = new Label(toolGroup, SWT.NONE);
	    label.setText("Composers:");
	    toolCB = new Combo(toolGroup, SWT.READ_ONLY | SWT.DROP_DOWN);
	    toolCB.setLayoutData(new GridData(GridData.FILL_BOTH));
	    
	    final Label descriptionLabel = new Label(toolGroup, SWT.NONE);
	    GridData gridData2 = new GridData(GridData.FILL_BOTH);
		gridData2.horizontalSpan = 2;
	    descriptionLabel.setLayoutData(gridData2);
	    
	    StringBuilder descriptionStringBuilder = new StringBuilder();
	    descriptionStringBuilder.append("Possible choices are:\n\n");
	    List<IComposerExtension> composerExtensions = ComposerExtensionManager.getInstance().getComposers();
	    extensions = new IComposerExtensionBase[composerExtensions.size()]; 
	    composerExtensions.toArray(extensions);
	    Arrays.sort(extensions, new Comparator<IComposerExtensionBase> () {
			public int compare(IComposerExtensionBase arg0, IComposerExtensionBase arg1) {
				return arg0.getName().compareTo(arg1.getName());
			}
	    });
	    
		for (IComposerExtensionBase composerExtension : extensions) {
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
			public void modifyText(ModifyEvent e) {
				composerExtension = extensions[toolCB.getSelectionIndex()];
			}
		});
		toolCB.select(0);
		
		//Path Group
		pathGroup = new Group(container, SWT.NONE);
		layout.numColumns = 2;
		layout.verticalSpacing = 9;
		pathGroup.setText("Path Specification:");
		pathGroup.setLayoutData(gd);
		pathGroup.setLayout(layout);
		
		String tooltip = SETS_THE_PATH_OF_COMPOSED_FILES_;
		buildLabel = new Label(pathGroup, SWT.NULL);
		buildLabel.setText("&Source Path:");
		buildLabel.setToolTipText(tooltip);
		buildPath = new Text(pathGroup, SWT.BORDER | SWT.SINGLE);
		buildPath.setLayoutData(gd);
		buildPath.setText("src");
		buildPath.setToolTipText(tooltip);
		
		tooltip = SETS_THE_PATH_OF_FEATUREFOLDERS_;
		label = new Label(pathGroup, SWT.NULL);
		label.setText("&Feature Path:");
		label.setToolTipText(tooltip);
		sourcePath = new Text(pathGroup, SWT.BORDER | SWT.SINGLE);
		sourcePath.setLayoutData(gd);
		sourcePath.setText(FEATURES);
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
	
	public IComposerExtensionBase getCompositionTool() {
		return composerExtension;
	}
	
	public boolean hasCompositionTool() {
		return composerExtension != null;
	}
	
	protected void addListeners() {
		toolCB.addModifyListener(new ModifyListener() {
			
			@Override
			public void modifyText(ModifyEvent e) {
				dialogChanged();
			}
		});
		
		sourcePath.addModifyListener(new ModifyListener() {
			
			@Override
			public void modifyText(ModifyEvent e) {
				dialogChanged();
			}
		});
		
		buildPath.addModifyListener(new ModifyListener() {
			
			@Override
			public void modifyText(ModifyEvent e) {
				dialogChanged();
			}
		});
		
		configsPath.addModifyListener(new ModifyListener() {
	
			@Override
			public void modifyText(ModifyEvent e) {
				dialogChanged();
			}
		});
	}
	
	protected void dialogChanged() {
		IComposerExtensionBase compositionTool = getCompositionTool();
		sourcePath.setEnabled(compositionTool.hasFeatureFolder());
		buildPath.setEnabled(compositionTool.hasSourceFolder());
		
		if (isEnabled(sourcePath) && isEnabled(configsPath) &&
				getSourcePath().equals(getConfigPath())) {
			updateStatus(SOURCE_PATH_EQUALS_CONFIGURATIONS_PATH_);
			return;
		}
		if (isEnabled(sourcePath) && isEnabled(buildPath) &&
				getSourcePath().equals(getBuildPath())) {
			updateStatus(SOURCE_PATH_EQUALS_BUILD_PATH_);
			return;
		}
		if (isEnabled(buildPath) && isEnabled(configsPath) && 
				getBuildPath().equals(getConfigPath())) {
			updateStatus(BUILD_PATH_EQUALS_CONFIGURATIONS_PATH_);
			return;
		}
		if (isEnabled(sourcePath) && isPathEmpty(getSourcePath(), SOURCE))return;
		if (isEnabled(buildPath) && isPathEmpty(getBuildPath(), BUILD))return;
		if (isEnabled(configsPath) && isPathEmpty(getConfigPath(), EQUATIONS))return;
		
		if (isEnabled(sourcePath) && isInvalidPath(getSourcePath(), SOURCE))return;
		if (isEnabled(buildPath) && isInvalidPath(getBuildPath(), BUILD))return;
		if (isEnabled(configsPath) && isInvalidPath(getConfigPath(), EQUATIONS))return;
		
		if (compositionTool.supportsAndroid()) {
			
			canFlipToNextPage = false;
			setErrorMessage(null);
			setPageComplete(true);
			
			if (getSourcePath().equals("src") || getSourcePath().equals("res")) {
				updateStatus(SOURCE_PATH_RESTRICTION_ANDROID);
				return;
			}
			if (getBuildPath().equals("src") || getBuildPath().equals("res")) {
				updateStatus(BUILD_PATH_RESTRICTION_ANDROID);
				return;
			}
			if (getConfigPath().equals("src") || getConfigPath().equals("res")) {
				updateStatus(CONFIG_PATH_RESTRICTION_ANDROID);
				return;
			}
			
			return;
		}
		
		updateStatus(null);
	}

	protected boolean isEnabled(Text text) {
		if (text.isEnabled() && text.isVisible()) {
			return true;
		}
		return false;
	}

	protected boolean isPathEmpty(String path, String name) {
		if (path.length() == 0) {
			updateStatus(name + PATH_MUST_BE_SPECIFIED_);
			canFlipToNextPage  = false;
			return true;
		}
		canFlipToNextPage  = true;
		return false;
	}
	protected boolean isInvalidPath(String path, String name) {
		if (path.contains("*")
				|| path.contains("?")
				|| path.startsWith(".")
				|| path.endsWith(".")
				|| path.contains("//")
				|| path.endsWith("/")
				|| path.endsWith("/")
				|| path.contains("/.")
				|| path.contains("./")
				|| path.contains("<")
				|| path.contains(">")
				|| path.contains("|")
				|| path.contains(""+'"')) {
			updateStatus(name + PATH_MUST_BE_VALID);
			return true;
		}
		return false;
	}
	
	protected void updateStatus(String message) {
		setErrorMessage(message);
		setPageComplete(message == null);
	}
	
	public String getSourcePath() {
		if (sourcePath.isEnabled()) {
			return sourcePath.getText();
		} else {
			return getBuildPath();
		}
	}
	
	public String getConfigPath() {
		return configsPath.isEnabled() ? configsPath.getText() : "";

	}
	
	public String getBuildPath() {
		return buildPath.getText();
	}

	public boolean canFlipToNextPage() {
		return this.canFlipToNextPage;
	}
}
