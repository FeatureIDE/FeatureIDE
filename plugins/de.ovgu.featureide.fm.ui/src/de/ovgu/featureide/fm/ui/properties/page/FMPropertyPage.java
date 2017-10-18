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
package de.ovgu.featureide.fm.ui.properties.page;

import static de.ovgu.featureide.fm.core.localization.StringTable.EXPORT;
import static de.ovgu.featureide.fm.core.localization.StringTable.IMPORT;

import java.io.File;
import java.util.LinkedList;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.preference.ColorSelector;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.PropertyPage;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIBasics;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManagerDefaults;
import de.ovgu.featureide.fm.ui.properties.language.English;
import de.ovgu.featureide.fm.ui.properties.language.ILanguage;

/**
 * At this property page, feature model specific settings can be specified
 *
 * @author Jens Meinicke
 */
public class FMPropertyPage extends PropertyPage implements IFMPropertyPage, GUIDefaults {

	/* legend group objects: */
	Combo languageCombo;
	Button buttonHideLegend;
	LinkedList<ILanguage> languages = new LinkedList<ILanguage>();

	/* spaces group objects: */
	Text textMarginX, textMarginY, textFeatureX, textFeatureY, textConstraint;

	/* color group objects: */
	ColorSelector selectorLegendBackground, selectorConcreteBackground, selectorAbstractBackground, selectorDeadBackground, selectorLegendBorder,
			selectorDiagramBackground, selectorConstraint, selectorConnection, selectorWarning;
	// selectorHiddenBackground
	static ColorSelector selectorFeatureBorder;
	Button buttonHideBorderColor;

	public FMPropertyPage() {

	}

	@Override
	protected Control createContents(Composite parent) {
		final Composite composite = new Composite(parent, SWT.NULL);
		final GridLayout layout = new GridLayout();
		layout.numColumns = 1;
		layout.verticalSpacing = 9;
		composite.setLayout(layout);

		addLegendGroup(composite);
		addSpacesGroup(composite);
		addColorGroup(composite);
		// addExtensionsGroup(composite);
		return composite;
	}

	/**
	 * Creates the group to specify legend specific settings.
	 */
	private void addLegendGroup(Composite composite) {
		final Group group = createGroup(composite, LEGEND_GROUP_TEXT);
		getLanguageExtensions();

		Label label = new Label(group, SWT.NULL);
		label.setText(LEGEND_HIDE_LABEL);
		buttonHideLegend = new Button(group, SWT.CHECK);
		final GridData gd = new GridData(GridData.BEGINNING);
		buttonHideLegend.setLayoutData(gd);
		buttonHideLegend.setSelection(FMPropertyManager.isLegendHidden());

		label = new Label(group, SWT.NULL);
		label.setText(LEGEND_LANGUAGE_LABEL);
		languageCombo = new Combo(group, SWT.READ_ONLY | SWT.DROP_DOWN);
		languageCombo.setLayoutData(new GridData(GridData.FILL));

		for (final ILanguage l : languages) {
			languageCombo.add(l.getName());
		}
		languageCombo.setText(English.NAME);
		int i = 0;
		for (final String language : languageCombo.getItems()) {
			if (language.equals(FMPropertyManager.getLanguage().getName())) {
				languageCombo.select(i);
				break;
			}
			i++;
		}

		selectorLegendBackground =
			createSelectorEntry(group, LEGEND_BACKGROUND_LABEL, FMPropertyManager.getLegendBackgroundColor().getRGB(), LEGEND_BACKGROUND__TIP);
		selectorLegendBorder = createSelectorEntry(group, LEGEND_BORDER_LABEL, FMPropertyManager.getLegendBorderColor().getRGB(), LEGEND_BORDER_TIP);
	}

	/**
	 * Creates the group to specify model specific spaces.
	 *
	 * @param composite
	 */
	private void addSpacesGroup(Composite composite) {
		final Group group = createGroup(composite, SPACES_GROUP_TEXT);

		textMarginX = createTextEntry(group, SPACES_MARGIN_X, FMPropertyManager.getLayoutMarginX(), SPACES_TIP_MARGIN_X);
		textMarginY = createTextEntry(group, SPACES_MARGIN_Y, FMPropertyManager.getLayoutMarginY(), SPACES_TIP_MARGIN_Y);
		textFeatureX = createTextEntry(group, SPACES_FEATURE_X, FMPropertyManager.getFeatureSpaceX(), SPACES_TIP_FEATURE_X);
		textFeatureY = createTextEntry(group, SPACES_FEATURE_Y, FMPropertyManager.getFeatureSpaceY() - SPECES_FEATURE_X_ADJUST, SPACES_TIP_FEATURE_Y);
		textConstraint = createTextEntry(group, SPACES_CONSTRAINT, FMPropertyManager.getConstraintSpace() - SPECES_CONSTRAIT_ADJUST, SPACES_TIP_CONSTRIANT);
	}

	/**
	 * Creates the group to specify model specific colors.
	 *
	 * @param composite
	 */
	private void addColorGroup(Composite composite) {
		final Group colorGroup = createGroup(composite, COLOR_GROUP_TEXT);

		selectorDiagramBackground =
			createSelectorEntry(colorGroup, COLOR_DIAGRAM_LABEL, FMPropertyManager.getDiagramBackgroundColor().getRGB(), COLOR_BACKGROUND_TIP);
		selectorConcreteBackground =
			createSelectorEntry(colorGroup, COLOR_CONCRETE_LABEL, FMPropertyManager.getConcreteFeatureBackgroundColor().getRGB(), COLOR_CONCRETE_TIP);
		selectorAbstractBackground =
			createSelectorEntry(colorGroup, COLOR_ABSTRACT_LABEL, FMPropertyManager.getAbstractFeatureBackgroundColor().getRGB(), COLOR_ABSTRACT_TIP);

		final Label label = new Label(colorGroup, SWT.NULL);
		label.setText(HIDE_BORDER_COLOR);
		label.setToolTipText(COLOR_CHECKBOX_TIP);
		buttonHideBorderColor = new Button(colorGroup, SWT.CHECK);
		final GridData gd = new GridData(GridData.BEGINNING);
		buttonHideBorderColor.setLayoutData(gd);
		buttonHideBorderColor.setSelection(FMPropertyManager.isBorderColorHidden());

		selectorFeatureBorder = createSelectorEntry(colorGroup, COLOR_BORDER, FMPropertyManager.getFeatureBorderColor().getRGB(), COLOR_BORDER_TIP);
		// selectorHiddenBackground = createSelectorEntry(colorGroup, COLOR_HIDDEN, PersistentPropertyManager.getHiddenFeatureBackgroundColor().getRGB(),
		// COLOR_HIDDEN_TIP);
		selectorConnection = createSelectorEntry(colorGroup, COLOR_CONNECTION, FMPropertyManager.getConnectionForegroundColor().getRGB(), COLOR_CONNECTION_TIP);
		selectorConstraint = createSelectorEntry(colorGroup, COLOR_CONSTRAINT, FMPropertyManager.getConstraintBackgroundColor().getRGB(), COLOR_CONSTRAINT_TIP);
		selectorWarning = createSelectorEntry(colorGroup, COLOR_WARNING, FMPropertyManager.getWarningColor().getRGB(), COLOR_WARNING_TIP);
		selectorDeadBackground = createSelectorEntry(colorGroup, COLOR_ERROR, FMPropertyManager.getDeadFeatureBackgroundColor().getRGB(), COLOR_DEAD_TIP);

		if (buttonHideBorderColor.getSelection()) {
			selectorFeatureBorder.setEnabled(true);
		} else {
			selectorFeatureBorder.setEnabled(false);
		}

		buttonHideBorderColor.addSelectionListener(new SelectionListener() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				if (buttonHideBorderColor.getSelection()) {
					selectorFeatureBorder.setColorValue(FMPropertyManager.getFeatureBorderColorSave().getRGB());
					selectorFeatureBorder.setEnabled(true);
				} else {
					FMPropertyManager.setFeatureBorderColorSave(GUIBasics.createColor(selectorFeatureBorder.getColorValue().red,
							selectorFeatureBorder.getColorValue().green, selectorFeatureBorder.getColorValue().blue));
					selectorFeatureBorder.setEnabled(false);
					selectorFeatureBorder.setColorValue(GUIDefaults.CONCRETE_BORDER_COLOR.getRGB());
				}
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {

			}

		});
	}

	/**
	 * Add the export and import buttons to the button group on the bottom of the dialog.
	 */
	@Override
	protected void contributeButtons(Composite buttonBar) {
		final GridLayout layout = new GridLayout();
		layout.numColumns = 4;
		layout.marginHeight = 0;
		layout.marginWidth = 0;
		layout.makeColumnsEqualWidth = false;
		buttonBar.setLayout(layout);

		final int widthHint = convertHorizontalDLUsToPixels(IDialogConstants.BUTTON_WIDTH);
		final Button importButton = new Button(buttonBar, SWT.PUSH);
		importButton.setText(IMPORT);
		GridData data = new GridData(GridData.HORIZONTAL_ALIGN_FILL);
		Point minButtonSize = importButton.computeSize(SWT.DEFAULT, SWT.DEFAULT, true);
		data.widthHint = Math.max(widthHint, minButtonSize.x);
		importButton.setLayoutData(data);
		importButton.addSelectionListener(new SelectionAdapter() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				performImport();
			}
		});

		final Button exportButton = new Button(buttonBar, SWT.PUSH);
		exportButton.setText(EXPORT);
		data = new GridData(GridData.HORIZONTAL_ALIGN_FILL);
		minButtonSize = exportButton.computeSize(SWT.DEFAULT, SWT.DEFAULT, true);
		data.widthHint = Math.max(widthHint, minButtonSize.x);
		exportButton.setLayoutData(data);
		exportButton.addSelectionListener(new SelectionAdapter() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				performExport();
			}
		});

	}

	private void performImport() {
		final FileDialog importDialog = new FileDialog(new Shell(), SWT.OPEN);
		if (importDialog.open() != null) {
			new SettingsImport(new File(importDialog.getFilterPath() + "\\" + importDialog.getFileName()));
			update();
		}
	}

	private void performExport() {
		applySettings();
		final FileDialog exportDialog = new FileDialog(new Shell(), SWT.SAVE);
		exportDialog.setFilterPath(FMPropertyManagerDefaults.workspaceRoot.getLocation().toOSString());
		exportDialog.setFilterIndex(0);
		if (exportDialog.open() != null) {
			new SettingsExport(new File(exportDialog.getFilterPath() + "\\" + exportDialog.getFileName()));
		}
	}

	/**
	 * Creates a new {@link Group}
	 *
	 * @param composite The composite of the group
	 * @param text The label of the group
	 * @return The created group
	 */
	private Group createGroup(Composite composite, String text) {
		final Group group = new Group(composite, SWT.NONE);
		group.setText(text);
		group.setLayoutData(new GridData(GridData.FILL_BOTH));
		final GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		group.setLayout(layout);
		return group;
	}

	/**
	 * Creates a label and a {@link Text} with the given parameters.
	 *
	 * @param group The group containing the text field
	 * @param labelText The text of the label
	 * @param value The numerical entry of the text filed
	 * @param toolTipText
	 * @return The created text field
	 */
	private Text createTextEntry(Group group, String labelText, int value, String toolTipText) {
		final Label label = new Label(group, SWT.NULL);
		label.setText(labelText);
		label.setToolTipText(toolTipText);
		final Text text = new Text(group, SWT.BORDER | SWT.SINGLE);
		text.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		text.setText(Integer.toString(value));
		return text;
	}

	/**
	 * Creates a label and a {@link ColorSelector} with the given parameters.
	 *
	 * @param group The group containing the ColorSelecotr
	 * @param labelText The text of the label
	 * @param rgb The value of the color selector
	 * @return The created ColorSelector
	 */
	private ColorSelector createSelectorEntry(Group group, String labelText, RGB rgb, String toolTipText) {
		final Label label = new Label(group, SWT.NULL);
		label.setText(labelText);
		label.setToolTipText(toolTipText);
		final ColorSelector selector = new ColorSelector(group);
		selector.setColorValue(rgb);
		return selector;
	}

	@Override
	public String getDescription() {
		return DESCRIPTION;
	}

	@Override
	public boolean performOk() {
		applySettings();
		return super.performOk();
	}

	@Override
	protected void performApply() {
		applySettings();
		super.performApply();
	}

	private void applySettings() {
		FMPropertyManager.reset();
		performLegendGroup();
		performSpecesGroup();
		performFeatureGroup();
		FMPropertyManager.updateEditors();
	}

	/**
	 * Saves the selected values for: legend group
	 */
	private void performLegendGroup() {
		FMPropertyManager.setHideLegend(buttonHideLegend.getSelection());
		FMPropertyManager.setLanguage(languageCombo.getText());
		FMPropertyManager.setLegendBackgroundColor(new Color(null, selectorLegendBackground.getColorValue()));
		FMPropertyManager.setLegendBorderColor(new Color(null, selectorLegendBorder.getColorValue()));
	}

	/**
	 * Saves the selected values for: spaces group
	 */
	private void performSpecesGroup() {
		FMPropertyManager.setlayoutMagrginX(Integer.parseInt(textMarginX.getText()));
		FMPropertyManager.setlayoutMagrginY(Integer.parseInt(textMarginY.getText()));
		FMPropertyManager.setFeatureSpaceX(Integer.parseInt(textFeatureX.getText()));
		FMPropertyManager.setFeatureSpaceY(Integer.parseInt(textFeatureY.getText()) + SPECES_FEATURE_X_ADJUST);
		FMPropertyManager.setConstraintSpace(Integer.parseInt(textConstraint.getText()) + SPECES_CONSTRAIT_ADJUST);
	}

	/**
	 * Saves the selected values for: feature group
	 */
	private void performFeatureGroup() {
		FMPropertyManager.setDiagramBackgroundColor(new Color(null, selectorDiagramBackground.getColorValue()));
		FMPropertyManager.setConcreteFeatureBackgroundColor(new Color(null, selectorConcreteBackground.getColorValue()));
		FMPropertyManager.setAbstractFeatureBackgroundColor(new Color(null, selectorAbstractBackground.getColorValue()));
		// PersistentPropertyManager.setHiddenFeatureBackgroundColor(new Color(null, selectorHiddenBackground.getColorValue()));
		FMPropertyManager.setDeadFeatureBackgroundColor(new Color(null, selectorDeadBackground.getColorValue()));
		FMPropertyManager.setConstraintBackgroundColor(new Color(null, selectorConstraint.getColorValue()));
		FMPropertyManager.setConnectionForegroundColor(new Color(null, selectorConnection.getColorValue()));
		FMPropertyManager.setWarningColor(new Color(null, selectorWarning.getColorValue()));
		FMPropertyManager.setFeatureBorderColor(new Color(null, selectorFeatureBorder.getColorValue()));
		FMPropertyManager.setHideBorderColor(buttonHideBorderColor.getSelection());
	}

	@Override
	protected void performDefaults() {
		resetLegendGroup();
		resetSpecesGroup();
		resetFeatureGroup();
		super.performDefaults();
	}

	/**
	 * Sets the default values at: legend group.
	 */
	private void resetLegendGroup() {
		buttonHideLegend.setSelection(false);
		languageCombo.select(0);
		selectorLegendBorder.setColorValue(LEGEND_BORDER_COLOR.getRGB());
		selectorLegendBackground.setColorValue(LEGEND_BACKGROUND.getRGB());
	}

	/**
	 * Sets the default values at: spaces group.
	 */
	private void resetSpecesGroup() {
		textMarginX.setText(Integer.toString(LAYOUT_MARGIN_X));
		textMarginY.setText(Integer.toString(LAYOUT_MARGIN_Y));
		textFeatureX.setText(Integer.toString(FEATURE_SPACE_X));
		textFeatureY.setText(Integer.toString(FEATURE_SPACE_Y - SPECES_FEATURE_X_ADJUST));
		textConstraint.setText(Integer.toString(CONSTRAINT_SPACE_Y - SPECES_CONSTRAIT_ADJUST));
	}

	/**
	 * Sets the default values at: feature group.
	 */
	private void resetFeatureGroup() {
		selectorDiagramBackground.setColorValue(DIAGRAM_BACKGROUND.getRGB());
		selectorConcreteBackground.setColorValue(CONCRETE_BACKGROUND.getRGB());
		selectorAbstractBackground.setColorValue(ABSTRACT_BACKGROUND.getRGB());
		// selectorHiddenBackground.setColorValue(HIDDEN_BACKGROUND.getRGB());
		selectorDeadBackground.setColorValue(DEAD_BACKGROUND.getRGB());
		selectorConstraint.setColorValue(CONSTRAINT_BACKGROUND.getRGB());
		selectorConnection.setColorValue(CONNECTION_FOREGROUND.getRGB());
		selectorWarning.setColorValue(WARNING_BACKGROUND.getRGB());
		selectorFeatureBorder.setColorValue(CONCRETE_BORDER_COLOR.getRGB());
		selectorFeatureBorder.setEnabled(false);
		buttonHideBorderColor.setSelection(false);
	}

	/**
	 * Fills the List LANGUAGES with all defines languages at the extension point "de.ovgu.featureide.fm.core.language".
	 */
	private void getLanguageExtensions() {
		final IConfigurationElement[] config = Platform.getExtensionRegistry().getConfigurationElementsFor(FMUIPlugin.PLUGIN_ID + ".language");
		try {
			for (final IConfigurationElement e : config) {
				final Object o = e.createExecutableExtension("class");
				if (o instanceof ILanguage) {
					languages.add(((ILanguage) o));
				}
			}
		} catch (final Exception e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	private void update() {
		updateLegendGroup();
		updateSpecesGroup();
		updateFeatureGroup();
	}

	/**
	 * Sets the default values at: legend group.
	 */
	private void updateLegendGroup() {
		buttonHideLegend.setSelection(FMPropertyManager.isLegendHidden());
		languageCombo.setText(English.NAME);
		int i = 0;
		for (final String language : languageCombo.getItems()) {
			if (language.equals(FMPropertyManager.getLanguage().getName())) {
				languageCombo.select(i);
				break;
			}
			i++;
		}
		selectorLegendBorder.setColorValue(FMPropertyManager.getLegendBorderColor().getRGB());
		selectorLegendBackground.setColorValue(FMPropertyManager.getLegendBackgroundColor().getRGB());
	}

	/**
	 * Sets the default values at: spaces group.
	 */
	private void updateSpecesGroup() {
		textMarginX.setText(Integer.toString(FMPropertyManager.getLayoutMarginX()));
		textMarginY.setText(Integer.toString(FMPropertyManager.getLayoutMarginY()));
		textFeatureX.setText(Integer.toString(FMPropertyManager.getFeatureSpaceX()));
		textFeatureY.setText(Integer.toString(FMPropertyManager.getFeatureSpaceY() - SPECES_FEATURE_X_ADJUST));
		textConstraint.setText(Integer.toString(FMPropertyManager.getConstraintSpace() - SPECES_CONSTRAIT_ADJUST));
	}

	/**
	 * Sets the default values at: feature group.
	 */
	private void updateFeatureGroup() {
		selectorDiagramBackground.setColorValue(FMPropertyManager.getDiagramBackgroundColor().getRGB());
		selectorConcreteBackground.setColorValue(FMPropertyManager.getConcreteFeatureBackgroundColor().getRGB());
		selectorAbstractBackground.setColorValue(FMPropertyManager.getAbstractFeatureBackgroundColor().getRGB());
		// selectorHiddenBackground.setColorValue(PersistentPropertyManager.getHiddenFeatureBackgroundColor().getRGB());
		selectorDeadBackground.setColorValue(FMPropertyManager.getDeadFeatureBackgroundColor().getRGB());
		selectorConstraint.setColorValue(FMPropertyManager.getConstraintBackgroundColor().getRGB());
		selectorConnection.setColorValue(FMPropertyManager.getConnectionForegroundColor().getRGB());
		selectorWarning.setColorValue(FMPropertyManager.getWarningColor().getRGB());
		selectorFeatureBorder.setEnabled(FMPropertyManager.isBorderColorHidden());
		selectorFeatureBorder.setColorValue(FMPropertyManager.getFeatureBorderColor().getRGB());
		buttonHideBorderColor.setSelection(FMPropertyManager.isBorderColorHidden());
	}
}
