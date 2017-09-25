package br.ufal.ic.colligens.preferences;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;

import br.ufal.ic.colligens.activator.Colligens;

public class Initializer extends AbstractPreferenceInitializer {

	@Override
	public void initializeDefaultPreferences() {
		final IPreferenceStore store = Colligens.getDefault().getPreferenceStore();

		store.setDefault("FEATURE_MODEL", true);
		store.setDefault("USE_INCLUDES", false);
		store.setDefault("USE_STUBS", true);
		store.setDefault("TypeChefPreference", "--parse");

		// PreferenceGcc
		store.setDefault("GCC", "gcc");
		store.setDefault("LIBS", "");
		store.setDefault("SystemRoot", "/");
		store.setDefault("SystemIncludes", "/usr/include");

		// PreferenceCppChecker
		store.setDefault("CppCheck", "");

	}
}
