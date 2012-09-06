package de.ovgu.featureide.fm.ui.properties.page;

import java.io.File;
import java.util.LinkedList;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.preference.ColorSelector;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
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
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;
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
	ColorSelector selectorLegendBackground, selectorConcreteBackground, selectorAbstractBackground, 
		selectorDeadBackground, selectorLegendBorder, selectorDiagramBackground, selectorConstraint, selectorConnection,
		selectorWarning;
	//selectorHiddenBackground

	public FMPropertyPage() {

	}

	@Override
	protected Control createContents(Composite parent) {
		Composite composite = new Composite(parent, SWT.NULL);
		GridLayout layout = new GridLayout();
		layout.numColumns = 1;
		layout.verticalSpacing = 9;
		composite.setLayout(layout);
		
		addLegendGroup(composite);
		addSpacesGroup(composite);
		addColorGroup(composite);
//		addExtensionsGroup(composite);
		return composite;
	}

	/**
	 * Creates the group to specify legend specific settings.
	 */
	private void addLegendGroup(Composite composite) {
		Group group = createGroup(composite, LEGEND_GROUP_TEXT);
		getLanguageExtensions();
		
		Label label = new Label(group, SWT.NULL);
		label.setText(LEGEND_HIDE_LABEL);
		buttonHideLegend = new Button(group, SWT.CHECK);
		GridData gd = new GridData(GridData.BEGINNING);
		buttonHideLegend.setLayoutData(gd);
		buttonHideLegend.setSelection(FMPropertyManager.isLegendHidden());

		label = new Label(group, SWT.NULL);
		label.setText(LEGEND_LANGUAGE_LABEL);		
		languageCombo = new Combo(group, SWT.READ_ONLY | SWT.DROP_DOWN);
		languageCombo.setLayoutData(new GridData(GridData.FILL));

		for (ILanguage l : languages) {
			languageCombo.add(l.getName());
		}
		languageCombo.setText(English.name);
		int i = 0;
		for (String language : languageCombo.getItems()) {
			if (language.equals(FMPropertyManager.getLanguage().getName())) {
				languageCombo.select(i);
				break;
			}
			i++;
		}

		selectorLegendBackground = createSelectorEntry(group, LEGEND_BACKGROUND_LABEL, FMPropertyManager.getLegendBackgroundColor().getRGB(), LEGEND_BACKGROUND__TIP);
		selectorLegendBorder = createSelectorEntry(group, LEGEND_BORDER_LABEL, FMPropertyManager.getLegendBorderColor().getRGB(), LEGEND_BORDER_TIP);
	}

	/**
	 * Creates the group to specify model specific spaces.
	 * @param composite
	 */
	private void addSpacesGroup(Composite composite) {
		Group group = createGroup(composite, SPACES_GROUP_TEXT);

		textMarginX = createTextEntry(group, SPACES_MARGIN_X, FMPropertyManager.getLayoutMarginX(), SPACES_TIP_MARGIN_X);
		textMarginY = createTextEntry(group, SPACES_MARGIN_Y, FMPropertyManager.getLayoutMarginY(), SPACES_TIP_MARGIN_Y);
		textFeatureX = createTextEntry(group, SPACES_FEATURE_X, FMPropertyManager.getFeatureSpaceX(), SPACES_TIP_FEATURE_X);
		textFeatureY = createTextEntry(group, SPACES_FEATURE_Y, FMPropertyManager.getFeatureSpaceY() - SPECES_FEATURE_X_ADJUST, SPACES_TIP_FEATURE_Y);
		textConstraint = createTextEntry(group, SPACES_CONSTRAINT, FMPropertyManager.getConstraintSpace() - SPECES_CONSTRAIT_ADJUST, SPACES_TIP_CONSTRIANT);
	}

	/**
	 * Creates the group to specify model specific colors.
	 * @param composite
	 */
	private void addColorGroup(Composite composite) {
		Group colorGroup = createGroup(composite, COLOR_GROUP_TEXT);

		selectorDiagramBackground = createSelectorEntry(colorGroup, COLOR_DIAGRAM_LABEL,FMPropertyManager.getDiagramBackgroundColor().getRGB(), COLOR_BACKGROUND_TIP);
		selectorConcreteBackground = createSelectorEntry(colorGroup, COLOR_CONCRETE_LABEL, FMPropertyManager.getConcreteFeatureBackgroundColor().getRGB(), COLOR_CONCRETE_TIP);
		selectorAbstractBackground = createSelectorEntry(colorGroup, COLOR_ABSTRACT_LABEL, FMPropertyManager.getAbstractFeatureBackgroundColor().getRGB(), COLOR_ABSTRACT_TIP);
//		selectorHiddenBackground = createSelectorEntry(colorGroup, COLOR_HIDDEN, PersistentPropertyManager.getHiddenFeatureBackgroundColor().getRGB(), COLOR_HIDDEN_TIP);
		selectorConnection = createSelectorEntry(colorGroup, COLOR_CONNECTION, FMPropertyManager.getConnectionForgroundColor().getRGB(), COLOR_CONNECTION_TIP);
		selectorConstraint = createSelectorEntry(colorGroup, COLOR_CONSTRAINT, FMPropertyManager.getConstraintBackgroundColor().getRGB(), COLOR_CONSTRAINT_TIP);
		selectorWarning = createSelectorEntry(colorGroup, COLOR_WARNING, FMPropertyManager.getWarningColor().getRGB(), COLOR_WARNING_TIP);
		selectorDeadBackground = createSelectorEntry(colorGroup, COLOR_DEAD, FMPropertyManager.getDeadFeatureBackgroundColor().getRGB(), COLOR_DEAD_TIP);
	}
	
	/**
	 * Add the export and import buttons to the button group on the bottom of the dialog.
	 */
	@Override
	protected void contributeButtons(Composite buttonBar) {
		GridLayout layout = new GridLayout();
        layout.numColumns = 4;
        layout.marginHeight = 0;
        layout.marginWidth = 0;
        layout.makeColumnsEqualWidth = false;
        buttonBar.setLayout(layout);
        
		int widthHint = convertHorizontalDLUsToPixels(IDialogConstants.BUTTON_WIDTH);
		Button importButton = new Button(buttonBar, SWT.PUSH);
		importButton.setText("Import");
		GridData data = new GridData(GridData.HORIZONTAL_ALIGN_FILL);
		Point minButtonSize = importButton.computeSize(SWT.DEFAULT,
				SWT.DEFAULT, true);
		data.widthHint = Math.max(widthHint, minButtonSize.x);
		importButton.setLayoutData(data);
		importButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				performImport();
			}
		});

        Button exportButton = new Button(buttonBar, SWT.PUSH);
        exportButton.setText("Export");
		data = new GridData(GridData.HORIZONTAL_ALIGN_FILL);
		minButtonSize = exportButton.computeSize(SWT.DEFAULT, SWT.DEFAULT,
				true);
		data.widthHint = Math.max(widthHint, minButtonSize.x);
		exportButton.setLayoutData(data);
		exportButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				performExport();
			}
		});

	}

	private void performImport() {
		FileDialog x = new FileDialog(new Shell(),SWT.OPEN);
		x.open();
		String path = x.getFilterPath();
		String fileName = x.getFileName();
		File file = new File(path + "\\" + fileName);
		new SettingsImport(file);
		update();
		
	}
	
	private void performExport() {
		FileDialog x = new FileDialog(new Shell(),SWT.SAVE);
		x.setFilterPath(FMPropertyManager.workspaceRoot.getLocation().toOSString());
		x.setFilterIndex(0);
		x.open();
		String path = x.getFilterPath();
		String fileName = x.getFileName();
		new SettingsExport(new File(path + "\\" + fileName));
	}
	
	/**
	 * Creates a new {@link Group}
	 * @param composite The composite of the group
	 * @param text The label of the group
	 * @return The created group
	 */
	private Group createGroup(Composite composite, String text) {
		Group group = new Group(composite, SWT.NONE);
		group.setText(text);
		group.setLayoutData(new GridData(GridData.FILL_BOTH));
		GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		group.setLayout(layout);
		return group;
	}
	
	/**
	 * Creates a label and a {@link Text} with the given parameters.
	 * @param group The group containing the text field
	 * @param labelText The text of the label
	 * @param value The numerical entry of the text filed
	 * @param toolTipText 
	 * @return The created text field
	 */
	private Text createTextEntry(Group group, String labelText,
			int value, String toolTipText) {
		Label label = new Label(group, SWT.NULL);
		label.setText(labelText);
		label.setToolTipText(toolTipText);
		Text text = new Text(group, SWT.BORDER | SWT.SINGLE);
		text.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		text.setText(Integer.toString(value));
		return text;
	}
	
	/**
	 * Creates a label and a {@link ColorSelector} with the given parameters.
	 * @param group The group containing the ColorSelecotr
	 * @param labelText The text of the label
	 * @param rgb The value of the color selector
	 * @return The created ColorSelector
	 */
	private ColorSelector createSelectorEntry(Group group,
			String labelText, RGB rgb, String toolTipText) {
		Label label = new Label(group, SWT.NULL);
		label.setText(labelText);
		label.setToolTipText(toolTipText);
		ColorSelector selector = new ColorSelector(group);
		selector.setColorValue(rgb);
		return selector;
	}

	@Override
	public String getDescription() {
		return DESCRIPTION;
	}

	@Override
	public boolean performOk() {
		performLegendGroup();
		performSpecesGroup();
		performFeatureGroup();
		return super.performOk();
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
//		PersistentPropertyManager.setHiddenFeatureBackgroundColor(new Color(null, selectorHiddenBackground.getColorValue()));
		FMPropertyManager.setDeadFeatureBackgroundColor(new Color(null, selectorDeadBackground.getColorValue()));
		FMPropertyManager.setConstraintBackgroundColor(new Color(null, selectorConstraint.getColorValue()));
		FMPropertyManager.setConnectionForgroundColor(new Color(null, selectorConnection.getColorValue()));
		FMPropertyManager.setWarningColor(new Color(null, selectorWarning.getColorValue()));
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
//		selectorHiddenBackground.setColorValue(HIDDEN_BACKGROUND.getRGB());
		selectorDeadBackground.setColorValue(DEAD_BACKGROUND.getRGB());
		selectorConstraint.setColorValue(CONSTRAINT_BACKGROUND.getRGB());
		selectorConnection.setColorValue(CONNECTION_FOREGROUND.getRGB());
		selectorWarning.setColorValue(WARNING_BACKGROUND.getRGB());
	}
	
	/**
	 * Fills the List "languages" with all defines languages at the extension point 
	 * "de.ovgu.featureide.fm.core.language".
	 */
	private void getLanguageExtensions() {
		IConfigurationElement[] config = Platform.getExtensionRegistry()
				.getConfigurationElementsFor(FMUIPlugin.PLUGIN_ID + ".language");
		try {
			for (IConfigurationElement e : config) {
				final Object o = e.createExecutableExtension("class");
				if (o instanceof ILanguage) {
					languages.add(((ILanguage) o));
				}
			}
		} catch (Exception e) {
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
		languageCombo.setText(English.name);
		int i = 0;
		for (String language : languageCombo.getItems()) {
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
//		selectorHiddenBackground.setColorValue(PersistentPropertyManager.getHiddenFeatureBackgroundColor().getRGB());
		selectorDeadBackground.setColorValue(FMPropertyManager.getDeadFeatureBackgroundColor().getRGB());
		selectorConstraint.setColorValue(FMPropertyManager.getConstraintBackgroundColor().getRGB());
		selectorConnection.setColorValue(FMPropertyManager.getConnectionForgroundColor().getRGB());
		selectorWarning.setColorValue(FMPropertyManager.getWarningColor().getRGB());
	}
}
