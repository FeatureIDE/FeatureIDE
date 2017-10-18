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
package de.ovgu.featureide.core.propertypage;

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
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
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

	private IComposerExtensionBase composer = null;
	private Combo composerCombo;
	private Combo contractCombo;
	private Combo metaCombo;
	private Combo mechanismCombo;

	private boolean canFinish = true;

	private final ModifyListener listener = new ModifyListener() {

		@Override
		public void modifyText(ModifyEvent e) {
			dialogChanged();
		}

	};

	public FeatureProjectPropertyPage() {

	}

	@Override
	protected Control createContents(Composite parent) {

		final Composite composite = new Composite(parent, SWT.NONE);
		composite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		final GridLayout layout = new GridLayout();
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
		Label label = new Label(composite, SWT.NONE);
		label.setText("&Project: \t\t" + project.getName());
		label = new Label(composite, SWT.NONE);
		label.setText("&Compostion tool: " + composer.getName());
		label = new Label(composite, SWT.NONE);
		label.setText("&Contract Composition: " + featureProject.getContractComposition());
		label = new Label(composite, SWT.NONE);
		label.setText("&Metaproduct Generation: " + featureProject.getMetaProductGeneration());
		label = new Label(composite, SWT.NONE);
		label.setText("Composition mechanism: " + featureProject.getCompositionMechanism());
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

	/**
	 * Adds the composer combo box
	 *
	 * @param group
	 */
	private void addComposerMember(Group group) {
		final Label label = new Label(group, SWT.NULL);
		label.setText(COMPOSER_SELECTION_TEXT);
		composerCombo = new Combo(group, SWT.READ_ONLY | SWT.DROP_DOWN);
		composerCombo.setLayoutData(gd);

		final List<IComposerExtension> composerExtensions = ComposerExtensionManager.getInstance().getComposers();
		extensions = new IComposerExtensionBase[composerExtensions.size()];
		composerExtensions.toArray(extensions);
		Arrays.sort(extensions, new ExtensionComparator());

		for (final IComposerExtensionBase composerExtension : extensions) {
			composerCombo.add(composerExtension.getName());
		}

		final String composer = featureProject.getComposer().getName();
		int i = 0;
		for (final String item : composerCombo.getItems()) {
			if (item.equals(composer)) {
				composerCombo.select(i);
				break;
			}
			i++;
		}
		composerCombo.addModifyListener(listener);
	}

	/**
	 * Adds the composer combo box
	 *
	 * @param group
	 */
	private void addContractMember(Group group) {
		final Label label = new Label(group, SWT.NULL);
		label.setText(CONTRACT_SELECTION_TEXT);
		contractCombo = new Combo(group, SWT.READ_ONLY | SWT.DROP_DOWN);
		contractCombo.setLayoutData(gd);
		contractCombo.add(IFeatureProject.DEFAULT_CONTRACT_COMPOSITION);
		contractCombo.add(METHOD_BASED_COMPOSITION);
		contractCombo.add(EXPLICIT_CONTRACT_REFINEMENT);
		contractCombo.add(CONTRACT_OVERRIDING);
		contractCombo.add(CONJUNCTIVE_CONTRACT_REFINEMENT);
		contractCombo.add(CONSECUTIVE_CONTRACT_REFINEMENT);
		contractCombo.add(CUMULATIVE_CONTRACT_REFINEMENT);
		contractCombo.add(PLAIN_CONTRACTING);

		final String composer = featureProject.getContractComposition();
		refreshContractCombo(composer);
		contractCombo.addModifyListener(listener);
	}

	private void refreshContractCombo(String composer) {
		if (!this.composer.hasContractComposition()) {
			contractCombo.setEnabled(false);
			contractCombo.select(0);
		} else {
			int i = 0;
			for (final String item : contractCombo.getItems()) {
				if (item.equals(composer)) {
					contractCombo.select(i);
					break;
				}
				i++;
			}
		}
	}

	private void addMetaProductMember(Group group) {
		final Label label = new Label(group, SWT.NULL);
		label.setText("&Metaproduct Generation");
		metaCombo = new Combo(group, SWT.READ_ONLY | SWT.DROP_DOWN);
		metaCombo.setLayoutData(gd);
		metaCombo.add(IFeatureProject.META_THEOREM_PROVING);
		metaCombo.add(IFeatureProject.META_MODEL_CHECKING);
		metaCombo.add(IFeatureProject.META_MODEL_CHECKING_BDD_JAVA);
		metaCombo.add(IFeatureProject.META_MODEL_CHECKING_BDD_JAVA_JML);
		metaCombo.add(IFeatureProject.META_VAREXJ);
		// TODO reactivate this line if c metaproduct is supported
		// metaCombo.add(IFeatureProject.META_MODEL_CHECKING_BDD_C);
		final String selection = featureProject.getMetaProductGeneration();
		refreshMetaCombo(selection);
		metaCombo.addModifyListener(listener);
	}

	private void refreshMetaCombo(String selection) {
		if (!composer.hasMetaProductGeneration()) {
			metaCombo.setEnabled(false);
			metaCombo.select(0);
		} else {
			int i = 0;
			for (final String item : metaCombo.getItems()) {
				if (item.equals(selection)) {
					metaCombo.select(i);
					break;
				}
				i++;
			}
		}
	}

	private void addCompositionMechanismMember(Group group) {
		final Label label = new Label(group, SWT.NULL);
		label.setText(COMPOSITION_MECHANISM);
		mechanismCombo = new Combo(group, SWT.READ_ONLY | SWT.DROP_DOWN);
		mechanismCombo.setLayoutData(gd);

		for (final String mechanism : composer.getCompositionMechanisms()) {
			mechanismCombo.add(mechanism);
		}
		final String composer = featureProject.getCompositionMechanism();
		refreshCompositionMechanismCombo(composer);
		mechanismCombo.addModifyListener(listener);
	}

	private void refreshCompositionMechanismCombo(String compositionMechanism) {
		mechanismCombo.select(0);
		if (composer.getCompositionMechanisms().length == 0) {
			mechanismCombo.setEnabled(false);
		} else {
			int i = 0;
			for (final String item : mechanismCombo.getItems()) {
				if (item.equals(compositionMechanism)) {
					mechanismCombo.select(i);
					break;
				}
				i++;
			}
		}
	}

	/**
	 * Adds the text fields of features, source and configurations path
	 *
	 * @param group
	 */
	private void addAllPathMember(Group group) {
		// add feature path
		featurePath = addPathMember(group, COMPOSER_FEATURE_PATH, featureProject.getSourceFolder(), composer.hasFeatureFolder());
		// add source path
		sourcePath = addPathMember(group, COMPOSER_SOURCE_PATH, featureProject.getBuildFolder(), composer.hasSourceFolder());
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
		if (nothingChanged()) {
			return true;
		}
		setComposer();
		setPaths();
		setContractComposition();
		setMetaProductGeneration();
		setCompositionMechanism();
		try {
			/* update the FeatureProject settings */
			project.close(null);
			project.open(null);
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		return true;
	}

	private void setContractComposition() {
		if (!contractChanged()) {
			return;
		}

		featureProject.setContractComposition(contractCombo.getItem(contractCombo.getSelectionIndex()));

	}

	private boolean contractChanged() {
		return !featureProject.getContractComposition().equals(contractCombo.getText());

	}

	private void setMetaProductGeneration() {
		if (!metaProductChanged()) {
			return;
		}

		featureProject.setMetaProductGeneration(metaCombo.getItem(metaCombo.getSelectionIndex()));
	}

	private boolean metaProductChanged() {
		return !featureProject.getMetaProductGeneration().equals(metaCombo.getText());
	}

	private void setCompositionMechanism() {
		if (!compositionMechanismChanged()) {
			return;
		}

		featureProject.setCompositionMechanism(mechanismCombo.getItem(mechanismCombo.getSelectionIndex()));
	}

	private boolean compositionMechanismChanged() {
		return !featureProject.getCompositionMechanism().equals(mechanismCombo.getText());
	}

	/**
	 * Sets the composer of the feature project
	 */
	private void setComposer() {
		if (!composerChanged()) {
			return;
		}
		for (final IComposerExtensionBase c : extensions) {
			if (c.getName().equals(composerCombo.getItem(composerCombo.getSelectionIndex()))) {
				featureProject.setComposerID(c.getId());
			}
		}
	}

	/**
	 * Sets the paths of the feature project
	 */
	private void setPaths() {
		if (noPathChanged()) {
			return;
		}

		final IProject iProject = featureProject.getProject();
		createFolder(iProject.getFolder(featurePath.getText()));
		createFolder(iProject.getFolder(sourcePath.getText()));
		createFolder(iProject.getFolder(configPath.getText()));

		try {
			iProject.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		}

		featureProject.setPaths(featurePath.getText(), sourcePath.getText(), configPath.getText());
	}

	/**
	 * @param newFolder
	 */
	private void createFolder(IFolder newFolder) {
		final LinkedList<IFolder> parents = new LinkedList<IFolder>();
		IResource parent = newFolder;
		while (!parent.exists() && (parent instanceof IFolder)) {
			parents.addFirst((IFolder) parent);
			parent = parent.getParent();
		}
		for (final IFolder subFolder : parents) {
			try {
				subFolder.create(true, true, null);
			} catch (final CoreException e) {
				CorePlugin.getDefault().logError(e);
			}
		}
	}

	/**
	 * @return <code>true</code> if the shown settings are equal to the old
	 */
	private boolean nothingChanged() {
		return !composerChanged() && noPathChanged() && !contractChanged() && !metaProductChanged() && !compositionMechanismChanged();
	}

	/**
	 * @return
	 */
	private boolean composerChanged() {
		return !featureProject.getComposer().getName().equals(composerCombo.getText());
	}

	/**
	 * @return
	 */
	private boolean noPathChanged() {
		return ((featureProject.getSourceFolder() != null)
			? featureProject.getSourceFolder().getProjectRelativePath().toOSString().equals(featurePath.getText()) : true)
			&& ((featureProject.getBuildFolder() != null) ? featureProject.getBuildFolder().getProjectRelativePath().toOSString().equals(sourcePath.getText())
				: true)
			&& ((featureProject.getConfigFolder() != null) ? featureProject.getConfigFolder().getProjectRelativePath().toOSString().equals(configPath.getText())
				: true);
	}

	@Override
	protected void performDefaults() {
		final IComposerExtensionBase composer = featureProject.getComposer();
		int i = 0;
		for (final String item : composerCombo.getItems()) {
			if (item.equals(composer.getName())) {
				composerCombo.select(i);
				break;
			}
			i++;
		}
		i = 0;
		for (final String item : contractCombo.getItems()) {
			if (item.equals(featureProject.getContractComposition())) {
				contractCombo.select(i);
				break;
			}
			i++;
		}
		i = 0;
		for (final String item : metaCombo.getItems()) {
			if (item.equals(featureProject.getMetaProductGeneration())) {
				metaCombo.select(i);
				break;
			}
			i++;
		}
		i = 0;
		for (final String item : mechanismCombo.getItems()) {
			if (item.equals(featureProject.getCompositionMechanism())) {
				mechanismCombo.select(i);
				break;
			}
			i++;
		}
		featurePath.setEnabled(composer.hasFeatureFolder());
		featurePath.setText(featureProject.getSourceFolder().getProjectRelativePath().toOSString());
		sourcePath.setEnabled(composer.hasSourceFolder());
		sourcePath.setText(featureProject.getBuildFolder().getProjectRelativePath().toOSString());
		configPath.setText(featureProject.getConfigFolder().getProjectRelativePath().toOSString());
		refreshContractCombo(composerCombo.getText());
		refreshMetaCombo(metaCombo.getText());
		refreshCompositionMechanismCombo(mechanismCombo.getText());
	}

	/**
	 * Called if something at the dialog has been changed
	 */
	protected void dialogChanged() {
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
					if (featurePath.getText().equals("")) {
						updateStatus(DEFINE_A_FEATURES_PATH_);
						return;
					}
					if (featurePath.getText().equals(configPath.getText())) {
						updateStatus(CONFIGURATIONS_AND_FEATURES_PATH_SHOULD_DIFFER_);
						return;
					}
				} else {
					featurePath.setEnabled(false);
				}
				if (c.hasSourceFolder()) {
					sourcePath.setEnabled(true);
					if (sourcePath.getText().equals("")) {
						updateStatus(DEFINE_A_SOURCE_PATH_);
						return;
					}
					if (sourcePath.getText().equals(configPath.getText())) {
						updateStatus(CONFIGURATIONS_AND_SOURCE_PATH_SHOULD_DIFFER_);
						return;
					}
				} else {
					sourcePath.setEnabled(false);
				}
				if (c.hasFeatureFolder() && c.hasSourceFolder()) {
					if (featurePath.getText().equals(sourcePath.getText())) {
						updateStatus(SOURCE_AND_FEATURES_PATH_SHOULD_DIFFER_);
						return;
					}
				}

				if (configPath.getText().equals("")) {
					updateStatus(DEFINE_A_CONFIGURATIONS_PATH_);
					return;
				}
				if (!c.hasMetaProductGeneration()) {
					metaCombo.setEnabled(false);
					metaCombo.select(0);
				} else {
					metaCombo.setEnabled(true);
				}
				updateStatus(null);
				return;
			}
		}

	}

	/**
	 * Updates the error message
	 *
	 * @param message
	 */
	protected void updateStatus(String message) {
		setErrorMessage(message);
		if (message == null) {
			getApplyButton().setEnabled(true);
			canFinish = true;
		} else {
			getApplyButton().setEnabled(false);
			canFinish = false;
		}
	}
}
