package br.ufal.ic.colligens.preferences;

import static de.ovgu.featureide.fm.core.localization.StringTable.ANALYZING_IFDEF_VARIABILITY_IN_C_CODE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.GENERAL_PROCESSING_TYPECHEF_OPTIONS;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.RadioGroupFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

import br.ufal.ic.colligens.activator.Colligens;

public class PreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {

	public static final String ID = Colligens.PLUGIN_ID + ".preferences.PreferencePage";

	public PreferencePage() {
		super(GRID);

	}

	@Override
	public void createFieldEditors() {

		addField(new BooleanFieldEditor("FEATURE_MODEL", "&Feature Model", getFieldEditorParent()));

		addField(new BooleanFieldEditor("USE_INCLUDES", "U&se #includes (slower)", getFieldEditorParent()));

		addField(new BooleanFieldEditor("USE_STUBS", "Us&e stubs", getFieldEditorParent()));

		addField(new RadioGroupFieldEditor("TypeChefPreference", GENERAL_PROCESSING_TYPECHEF_OPTIONS, 1,
				new String[][] { { "&Typecheck", "--typecheck" }, { "P&arse", "--parse" } }, getFieldEditorParent()));

	}

	@Override
	public void init(IWorkbench workbench) {
		setPreferenceStore(Colligens.getDefault().getPreferenceStore());
		setDescription(ANALYZING_IFDEF_VARIABILITY_IN_C_CODE_);
	}

}
