package br.ufal.ic.colligens.preferences;

import static de.ovgu.featureide.fm.core.localization.StringTable.H;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.FileFieldEditor;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

import br.ufal.ic.colligens.activator.Colligens;

public class PreferenceCppChecker extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {

	public static final String ID = Colligens.PLUGIN_ID + ".preferences.PreferenceCppChecker";
	private FileFieldEditor fieldCppChecker;

	public PreferenceCppChecker() {
		super(GRID);
	}

	@Override
	public void createFieldEditors() {

		fieldCppChecker = new FileFieldEditor("CppCheck", "&CppCheck location:", getFieldEditorParent());
		addField(fieldCppChecker);

	}

	@Override
	public void init(IWorkbench workbench) {
		setPreferenceStore(Colligens.getDefault().getPreferenceStore());
		setDescription("CppCheck");
	}

	@Override
	public void propertyChange(PropertyChangeEvent event) {

		if (event.getProperty().equals("field_editor_value")) {
			// System.out.println(event.getSource());
			// field for which validation is required
			if (event.getSource() == fieldCppChecker) {
				// validation is successful
				final String value = fieldCppChecker.getStringValue();
				if (value != null) {
					try {
						final Runtime rt = Runtime.getRuntime();
						final Process pr = rt.exec(value + H);

						final BufferedReader input = new BufferedReader(new InputStreamReader(pr.getInputStream()));
						String line = null;
						while ((line = input.readLine()) != null) {
							if (line.contains("Cppcheck")) {
								setValid(true);
								setErrorMessage(null);
								super.performApply();
								super.propertyChange(event);
								input.close();
								return;
							}
						}

					} catch (final IOException e) {
						// e.printStackTrace();
					}
				}
				// validation fails

				setValid(false);
				setErrorMessage("Error: invalid program");

			}
		}
	}
}
