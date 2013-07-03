package br.ufal.ic.colligens.preferences;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;

import br.ufal.ic.colligens.activator.Colligens;

public class Initializer extends AbstractPreferenceInitializer {

	@Override
	public void initializeDefaultPreferences() {
		IPreferenceStore store = Colligens.getDefault()
				.getPreferenceStore();
		
		store.setDefault("FEATURE_MODEL", true);
		store.setDefault("GLOBAL_ANALYZE", true);
		store.setDefault("TypeChefPreference", "--parse");

		store.setDefault("GCC", "gcc");
		store.setDefault("LIBS", "");
		store.setDefault("SystemRoot", "/");
		store.setDefault("SystemIncludes", "/usr/include");
	}

}
