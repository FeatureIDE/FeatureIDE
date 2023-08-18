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
package de.ovgu.featureide.ui.propertypage;

import static de.ovgu.featureide.fm.core.localization.StringTable.COMPOSITION_MECHANISM;
import static de.ovgu.featureide.fm.core.localization.StringTable.COMPOSITION_TOOL_SETTINGS;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONFIGURATIONS_AND_FEATURES_PATH_SHOULD_DIFFER_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONFIGURATIONS_AND_SOURCE_PATH_SHOULD_DIFFER_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONJUNCTIVE_CONTRACT_REFINEMENT;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONSECUTIVE_CONTRACT_REFINEMENT;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONTRACT_OVERRIDING;
import static de.ovgu.featureide.fm.core.localization.StringTable.CUMULATIVE_CONTRACT_REFINEMENT;
import static de.ovgu.featureide.fm.core.localization.StringTable.DEFINE_A_CONFIGURATIONS_PATH_;
import static de.ovgu.featureide.fm.core.localization.StringTable.DEFINE_A_FEATURES_PATH_;
import static de.ovgu.featureide.fm.core.localization.StringTable.DEFINE_A_SOURCE_PATH_;
import static de.ovgu.featureide.fm.core.localization.StringTable.EXPLICIT_CONTRACT_REFINEMENT;
import static de.ovgu.featureide.fm.core.localization.StringTable.METHOD_BASED_COMPOSITION;
import static de.ovgu.featureide.fm.core.localization.StringTable.NO_RESOURCE_SELECTED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.PLAIN_CONTRACTING;
import static de.ovgu.featureide.fm.core.localization.StringTable.RESTRICTION;
import static de.ovgu.featureide.fm.core.localization.StringTable.SOURCE_AND_FEATURES_PATH_SHOULD_DIFFER_;

import java.io.Serializable;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.Objects;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.internal.core.JavaElement;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.PropertyPage;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.ComposerExtensionManager;
import de.ovgu.featureide.core.builder.IComposerExtension;
import de.ovgu.featureide.core.builder.IComposerExtensionBase;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.fm.core.FMCorePlugin;

/**
 * At this property page you can specify composer specific settings for a FeatureProject This property page specifies project specific settings
 *
 * @author Jens Meinicke
 */
// TODO distinction between rename and move of folders
// TODO change from FeatureModelling -> Antenna : Sourcepath is not written
@SuppressWarnings(RESTRICTION)
public class FeatureProjectPropertyPage extends PropertyPage {

	private static final class ExtensionComparator implements Comparator<IComposerExtensionBase>, Serializable {

		private static final long serialVersionUID = 1L;

		@Override
		public int compare(IComposerExtensionBase arg0, IComposerExtensionBase arg1) {
			return arg0.getName().compareTo(arg1.getName());
		}
	}

	private static final String DESCRIPTION = null;
	private static final String COMPOSER_GROUP_TEXT = COMPOSITION_TOOL_SETTINGS;
	private static final String COMPOSER_SELECTION_TEXT = "&Composition tool:";
	private static final String CONTRACT_SELECTION_TEXT = "&Contract composition:";
	private static final String COMPOSER_CONFIG_PATH = "&configurations path:";
	private static final String COMPOSER_FEATURE_PATH = "&Feature path:";
	private static final String COMPOSER_SOURCE_PATH = "&Source path:";

	private final GridData gd = new GridData(GridData.FILL_BOTH);

	private static IComposerExtensionBase[] extensions = null;
	private IProject project = null;
	private IFeatureProject featureProject = null;

	private Text sourcePath = null;
	private Text featurePath = null;
	private Text configPath = null;
	private Text featureModelPath = null;

	private IComposerExtensionBase composer = null;
	private Combo composerCombo;
	private Combo contractCombo;
	private Combo metaCombo;
	private Combo mechanismCombo;

	private boolean canFinish = true;
	private boolean updated = false;

	private final ModifyListener listener = new ModifyListener() {

		@Override
		public void modifyText(ModifyEvent e) {
			updateStatus(dialogChanged());
		}

	};

	@Override
	protected Control createContents(Composite parent) {
		final Composite composite = new Composite(parent, SWT.NONE);
		composite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		GridLayout layout = new GridLayout();
		layout.numColumns = 1;
		layout.verticalSpacing = 9;
		composite.setLayout(layout);

		if (!getProject()) {
			final Label label = new Label(composite, SWT.NONE);
			label.setText(NO_RESOURCE_SELECTED_);
			return composite;
		}

		featureProject = CorePlugin.getFeatureProject(project);
		if (featureProject == null) {
			final Label label = new Label(composite, SWT.NONE);
			label.setText("Project \"" + project.getName() + "\" is no FeatureIDE project.");
			return composite;
		}
		composer = featureProject.getComposer();

		final Composite labelGroup = new Composite(composite, SWT.NONE);
		labelGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		layout = new GridLayout();
		layout.numColumns = 2;
		labelGroup.setLayout(layout);

		new Label(labelGroup, SWT.NONE).setText("&Project: ");
		new Label(labelGroup, SWT.NONE).setText(project.getName());
		new Label(labelGroup, SWT.NONE).setText("&Compostion tool: ");
		if (composer != null) {
			new Label(labelGroup, SWT.NONE).setText(composer != null ? composer.getName() : "- none -");
			new Label(labelGroup, SWT.NONE).setText("&Contract Composition: ");
			new Label(labelGroup, SWT.NONE).setText(featureProject.getContractComposition());
			new Label(labelGroup, SWT.NONE).setText("&Metaproduct Generation: ");
			new Label(labelGroup, SWT.NONE).setText(featureProject.getMetaProductGeneration());
			new Label(labelGroup, SWT.NONE).setText("Composition mechanism: ");
			new Label(labelGroup, SWT.NONE).setText(featureProject.getCompositionMechanism());
		} else {
			new Label(labelGroup, SWT.NONE).setText("- none -");
			new Label(labelGroup, SWT.NONE).setText("&Contract Composition: ");
			new Label(labelGroup, SWT.NONE).setText("- none -");
			new Label(labelGroup, SWT.NONE).setText("&Metaproduct Generation: ");
			new Label(labelGroup, SWT.NONE).setText("- none -");
			new Label(labelGroup, SWT.NONE).setText("Composition mechanism: ");
			new Label(labelGroup, SWT.NONE).setText("- none -");
		}

		new Label(labelGroup, SWT.NONE).setText("Composition mechanism: ");
		new Label(labelGroup, SWT.NONE).setText("- none -");
		final Label label = new Label(labelGroup, SWT.NULL);
		label.setText("Feature model file: ");
		featureModelPath = new Text(labelGroup, SWT.BORDER | SWT.SINGLE);
		featureModelPath.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		featureModelPath.setText(FMCorePlugin.getPersitentModelFilePath(project).map(IPath::toString).orElse(""));
		featureModelPath.setEnabled(true);

		addCompositionGroup(composite);
		return composite;
	}

	/**
	 * Gets the project of the selected resource.
	 *
	 * @return <code>true</code> if successful
	 */
	private boolean getProject() {
		final IAdaptable resource = getElement();
		if (resource instanceof JavaElement) {
			final IJavaProject javaProject = ((JavaElement) resource).getJavaProject();
			project = javaProject.getProject();
		} else if (resource instanceof IResource) {
			project = ((IResource) resource).getProject();
		} else {
			return false;
		}
		return true;
	}

	/**
	 * Adds the group to specify composer specific settings
	 *
	 * @param composite
	 */
	private void addCompositionGroup(Composite composite) {
		final Group compositionGroup = new Group(composite, SWT.NONE);
		compositionGroup.setText(COMPOSER_GROUP_TEXT);
		compositionGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		final GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		compositionGroup.setLayout(layout);

		addComposerMember(compositionGroup);
		addAllPathMember(compositionGroup);
		addContractMember(compositionGroup);
		addMetaProductMember(compositionGroup);
		addCompositionMechanismMember(compositionGroup);
	}

	private void addComposerMember(Group group) {
		composerCombo = createCombo(group, COMPOSER_SELECTION_TEXT);
		extensions = ComposerExtensionManager.getInstance().getComposers().toArray(new IComposerExtension[0]);
		Arrays.sort(extensions, new ExtensionComparator());
		for (final IComposerExtensionBase composerExtension : extensions) {
			composerCombo.add(composerExtension.getName());
		}

		final IComposerExtensionClass composer = featureProject.getComposer();
		if (composer != null) {
			refreshCombo(composerCombo, true, composer.getName());
		}
		composerCombo.addModifyListener(listener);
	}

	private Combo createCombo(Group group, String labelText) {
		final Label label = new Label(group, SWT.NULL);
		label.setText(labelText);
		final Combo combo = new Combo(group, SWT.READ_ONLY | SWT.DROP_DOWN);
		combo.setLayoutData(gd);
		return combo;
	}

	private void refreshCombo(Combo combo, boolean enable, String value) {
		if (enable) {
			final String[] items = combo.getItems();
			final List<String> asList = Arrays.asList(items);
			final int valueIndex = asList.indexOf(value);
			if (valueIndex < 0) {
				combo.clearSelection();
			} else {
				combo.select(valueIndex);
			}
		} else {
			combo.setEnabled(false);
			combo.select(0);
		}
	}

	private void addContractMember(Group group) {
		contractCombo = createCombo(group, CONTRACT_SELECTION_TEXT);

		contractCombo.add(IFeatureProject.DEFAULT_CONTRACT_COMPOSITION);
		contractCombo.add(METHOD_BASED_COMPOSITION);
		contractCombo.add(EXPLICIT_CONTRACT_REFINEMENT);
		contractCombo.add(CONTRACT_OVERRIDING);
		contractCombo.add(CONJUNCTIVE_CONTRACT_REFINEMENT);
		contractCombo.add(CONSECUTIVE_CONTRACT_REFINEMENT);
		contractCombo.add(CUMULATIVE_CONTRACT_REFINEMENT);
		contractCombo.add(PLAIN_CONTRACTING);

		if (composer != null) {
			refreshCombo(contractCombo, composer.hasContractComposition(), featureProject.getContractComposition());
		}
		contractCombo.addModifyListener(listener);
	}

	private void addMetaProductMember(Group group) {
		metaCombo = createCombo(group, "&Metaproduct Generation");

		metaCombo.add(IFeatureProject.META_THEOREM_PROVING);
		metaCombo.add(IFeatureProject.META_MODEL_CHECKING);
		metaCombo.add(IFeatureProject.META_MODEL_CHECKING_BDD_JAVA);
		metaCombo.add(IFeatureProject.META_MODEL_CHECKING_BDD_JAVA_JML);
		metaCombo.add(IFeatureProject.META_VAREXJ);
		// TODO reactivate this line if c metaproduct is supported
		// metaCombo.add(IFeatureProject.META_MODEL_CHECKING_BDD_C);

		if (composer != null) {
			refreshCombo(metaCombo, composer.hasMetaProductGeneration(), featureProject.getMetaProductGeneration());
		}
		metaCombo.addModifyListener(listener);
	}

	private void addCompositionMechanismMember(Group group) {
		mechanismCombo = createCombo(group, COMPOSITION_MECHANISM);

		if (composer != null) {
			for (final String mechanism : composer.getCompositionMechanisms()) {
				mechanismCombo.add(mechanism);
			}
			refreshCombo(mechanismCombo, composer.getCompositionMechanisms().length > 0, featureProject.getCompositionMechanism());
		}

		mechanismCombo.addModifyListener(listener);
	}

	/**
	 * Adds the text fields of features, source and configurations path
	 *
	 * @param group
	 */
	private void addAllPathMember(Group group) {
		if (composer != null) {
			// add feature path
			featurePath = addPathMember(group, COMPOSER_FEATURE_PATH, featureProject.getSourceFolder(), composer.hasFeatureFolder());
			// add source path
			sourcePath = addPathMember(group, COMPOSER_SOURCE_PATH, featureProject.getBuildFolder(), composer.hasSourceFolder());
		} else {
			// add feature path
			featurePath = addPathMember(group, COMPOSER_FEATURE_PATH, null, false);
			// add source path
			sourcePath = addPathMember(group, COMPOSER_SOURCE_PATH, null, false);
		}
		// add configurations path
		configPath = addPathMember(group, COMPOSER_CONFIG_PATH, featureProject.getConfigFolder(), true);
	}

	/**
	 * Adds a path member with the given parameters
	 *
	 * @param group The group containing the member
	 * @param label The displayed label
	 * @param folder The associated folder
	 * @param enabeled The status of the member
	 * @return The created text field
	 */
	private Text addPathMember(Group group, String labelText, IFolder folder, boolean enabeled) {
		final Label label = new Label(group, SWT.NULL);
		label.setText(labelText);
		final Text text = new Text(group, SWT.BORDER | SWT.SINGLE);
		text.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		if (folder != null) {
			text.setText(folder.getProjectRelativePath().toOSString());
		}
		text.setEnabled(enabeled);
		text.addModifyListener(listener);
		return text;

	}

	@Override
	public String getDescription() {
		return DESCRIPTION;
	}

	@Override
	public boolean performOk() {
		if (!canFinish) {
			return false;
		}

		setFeatureModelFile();
		setComposer();
		setPaths();
		setContractComposition();
		setMetaProductGeneration();
		setCompositionMechanism();
		if (updated) {
			try {
				/* update the FeatureProject settings */
				project.close(null);
				project.open(null);
			} catch (final CoreException e) {
				CorePlugin.getDefault().logError(e);
			}
		}
		return true;
	}

	private void setFeatureModelFile() {
		final String text = featureModelPath.getText();
		if (!Objects.equals(text, FMCorePlugin.getPersitentModelFilePath(project).map(IPath::toString).orElse(null))) {
			FMCorePlugin.setPersitentModelFilePath(project, text.isBlank() ? null : text);
			updated = true;
		}
	}

	private void setContractComposition() {
		if (!featureProject.getContractComposition().equals(contractCombo.getText())) {
			featureProject.setContractComposition(contractCombo.getItem(contractCombo.getSelectionIndex()));
			updated = true;
		}
	}

	private void setMetaProductGeneration() {
		final String item = metaCombo.getItem(metaCombo.getSelectionIndex());
		if (!featureProject.getMetaProductGeneration().equals(item)) {
			featureProject.setMetaProductGeneration(item);
			updated = true;
		}
	}

	private void setCompositionMechanism() {
		if (mechanismCombo.getEnabled()) {
			final int selectionIndex = mechanismCombo.getSelectionIndex();
			if (selectionIndex >= 0) {
				final String item = mechanismCombo.getItem(selectionIndex);
				if (!featureProject.getCompositionMechanism().equals(item)) {
					featureProject.setCompositionMechanism(item);
					updated = true;
				}
			}
		}
	}

	/**
	 * Sets the composer of the feature project
	 */
	private void setComposer() {
		final IComposerExtensionClass composer = featureProject.getComposer();
		if ((composer != null) && !composer.getName().equals(composerCombo.getText())) {
			for (final IComposerExtensionBase c : extensions) {
				if (c.getName().equals(composerCombo.getItem(composerCombo.getSelectionIndex()))) {
					featureProject.setComposerID(c.getId());
					updated = true;
					break;
				}
			}
		}
	}

	/**
	 * Sets the paths of the feature project
	 */
	private void setPaths() {
		boolean pathsUpdates = false;
		final IProject project = featureProject.getProject();

		final String sourcePathText = featurePath.getText();
		FMCorePlugin.createFolder(project, sourcePathText);
		pathsUpdates |= hasChanged(featureProject.getSourceFolder(), sourcePathText);

		final String buildPathText = sourcePath.getText();
		FMCorePlugin.createFolder(project, buildPathText);
		pathsUpdates |= hasChanged(featureProject.getBuildFolder(), buildPathText);

		final String configPathText = configPath.getText();
		FMCorePlugin.createFolder(project, configPathText);
		pathsUpdates |= hasChanged(featureProject.getConfigFolder(), configPathText);

		if (pathsUpdates) {
			try {
				project.refreshLocal(IResource.DEPTH_INFINITE, null);
			} catch (final CoreException e) {
				CorePlugin.getDefault().logError(e);
			}

			featureProject.setPaths(sourcePathText, buildPathText, configPathText);
			updated = true;
		}
	}

	private boolean hasChanged(IFolder folder, String newFolderName) {
		return (folder == null) || Objects.equals(newFolderName, folder.getProjectRelativePath().toOSString());
	}

	@Override
	protected void performDefaults() {
		featurePath.setEnabled(composer != null ? composer.hasFeatureFolder() : false);
		featurePath.setText(getFolderText(featureProject.getSourceFolder()));
		sourcePath.setEnabled(composer != null ? composer.hasSourceFolder() : false);
		sourcePath.setText(getFolderText(featureProject.getBuildFolder()));
		configPath.setText(getFolderText(featureProject.getConfigFolder()));

		final IComposerExtensionClass currentComposer = featureProject.getComposer();
		if (currentComposer != null) {
			refreshCombo(composerCombo, true, currentComposer.getName());
		}
		if (composer != null) {
			refreshCombo(contractCombo, composer.hasContractComposition(), featureProject.getContractComposition());
			refreshCombo(metaCombo, composer.hasMetaProductGeneration(), featureProject.getMetaProductGeneration());
			refreshCombo(mechanismCombo, composer.getCompositionMechanisms().length > 0, featureProject.getCompositionMechanism());
		}
	}

	private String getFolderText(IFolder folder) {
		return folder == null ? "" : folder.getProjectRelativePath().toOSString();
	}

	/**
	 * Called if something at the dialog has been changed
	 */
	protected String dialogChanged() {
		for (final IComposerExtensionBase c : extensions) {
			if (c.getName().equals(composerCombo.getItem(composerCombo.getSelectionIndex()))) {
				if (!c.hasContractComposition()) {
					contractCombo.select(0); // set to none
					contractCombo.setEnabled(false);
				} else {
					contractCombo.setEnabled(true);
				}

				if (c.hasFeatureFolder()) {
					featurePath.setEnabled(true);
					if (featurePath.getText().trim().isEmpty()) {
						return DEFINE_A_FEATURES_PATH_;
					}
					if (featurePath.getText().equals(configPath.getText())) {
						return CONFIGURATIONS_AND_FEATURES_PATH_SHOULD_DIFFER_;
					}
				} else {
					featurePath.setEnabled(false);
				}
				if (c.hasSourceFolder()) {
					sourcePath.setEnabled(true);
					if (sourcePath.getText().trim().isEmpty()) {
						return DEFINE_A_SOURCE_PATH_;
					}
					if (sourcePath.getText().equals(configPath.getText())) {
						return CONFIGURATIONS_AND_SOURCE_PATH_SHOULD_DIFFER_;
					}
				} else {
					sourcePath.setEnabled(false);
				}
				if (c.hasFeatureFolder() && c.hasSourceFolder() && featurePath.getText().equals(sourcePath.getText())) {
					return SOURCE_AND_FEATURES_PATH_SHOULD_DIFFER_;
				}

				if (configPath.getText().trim().isEmpty()) {
					return DEFINE_A_CONFIGURATIONS_PATH_;
				}
				if (!c.hasMetaProductGeneration()) {
					metaCombo.setEnabled(false);
					metaCombo.select(0);
				} else {
					metaCombo.setEnabled(true);
				}
				break;
			}
		}
		return null;

	}

	/**
	 * Updates the error message
	 *
	 * @param message
	 */
	protected void updateStatus(String message) {
		setErrorMessage(message);
		getApplyButton().setEnabled(message == null);
		canFinish = message == null;
	}
}
