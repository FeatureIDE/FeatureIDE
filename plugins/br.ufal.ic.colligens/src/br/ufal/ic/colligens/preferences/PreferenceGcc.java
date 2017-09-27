package br.ufal.ic.colligens.preferences;

import static de.ovgu.featureide.fm.core.localization.StringTable.ANALYZING_IFDEF_VARIABILITY_IN_C_CODE_;

import org.eclipse.jface.preference.DirectoryFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

import br.ufal.ic.colligens.activator.Colligens;

public class PreferenceGcc extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {

	public static final String ID = Colligens.PLUGIN_ID + ".preferences.PreferenceGcc";

	public PreferenceGcc() {
		super(GRID);

	}

	@Override
	public void createFieldEditors() {

		addField(new StringFieldEditor("GCC", "Command:", getFieldEditorParent()));

		addField(new DirectoryFieldEditor("SystemRoot", "&System Root:", getFieldEditorParent()));

		addField(new DirectoryFieldEditor("SystemIncludes", "&System Includes:", getFieldEditorParent()));

		addField(new StringFieldEditor("LIBS", "Libs (gcc):", getFieldEditorParent()));

	}

	@Override
	public void init(IWorkbench workbench) {
		setPreferenceStore(Colligens.getDefault().getPreferenceStore());
		setDescription(ANALYZING_IFDEF_VARIABILITY_IN_C_CODE_);
	}

}
