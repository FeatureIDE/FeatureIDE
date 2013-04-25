package org.deltaj.transformations.rename;

import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.transformations.finder.DeltaJModuleReferenceFinder;

public class DeltaJModuleRenamer {

	private final DeltaModule deltaModule;
	private final String newName;

	public DeltaJModuleRenamer(DeltaModule deltaModule, String newName) {

		this.deltaModule = deltaModule;
		this.newName = newName;
	}

	public void rename() {

		setName();
		resetReferences();
	}

	private void setName() {

		deltaModule.setName(newName);
	}

	private void resetReferences() {

		for (ModuleReference moduleReference: new DeltaJModuleReferenceFinder(deltaModule).find()) {

			reset(moduleReference);
		}
	}

	private void reset(ModuleReference moduleReference) {

		moduleReference.setDeltaModule(null);
		moduleReference.setDeltaModule(deltaModule);
	}
}
