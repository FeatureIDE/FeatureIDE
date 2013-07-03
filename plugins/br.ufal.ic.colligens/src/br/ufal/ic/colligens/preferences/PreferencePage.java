package br.ufal.ic.colligens.preferences;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.RadioGroupFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

import br.ufal.ic.colligens.activator.Colligens;

public class PreferencePage extends FieldEditorPreferencePage implements
		IWorkbenchPreferencePage {
	public static final String ID = Colligens.PLUGIN_ID
			+ ".preferences.PreferencePage";

	public PreferencePage() {
		super(GRID);

	}

	@Override
	public void createFieldEditors() {

		addField(new BooleanFieldEditor("FEATURE_MODEL", "&Feature Model",
				getFieldEditorParent()));

		addField(new BooleanFieldEditor("GLOBAL_ANALYZE",
				"U&se #includes (slower)", getFieldEditorParent()));

		addField(new RadioGroupFieldEditor("TypeChefPreference",
				"TypeChef Preference ", 1, new String[][] {
						{ "&Typecheck", "--typecheck" },
						{ "P&arse", "--parse" } }, getFieldEditorParent()));

	}

	@Override
	public void init(IWorkbench workbench) {
		setPreferenceStore(Colligens.getDefault().getPreferenceStore());
		setDescription("Analyzing ifdef variability in C code.");
	}

}
