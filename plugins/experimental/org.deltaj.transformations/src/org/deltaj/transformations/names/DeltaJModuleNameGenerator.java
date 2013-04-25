package org.deltaj.transformations.names;

import java.util.Set;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.Program;
import org.deltaj.transformations.utils.SetFactory;

public class DeltaJModuleNameGenerator {

	private final Program program;

	public DeltaJModuleNameGenerator(Program program) {

		this.program = program;
	}

	public String generate(String suggestedName) {

		Set<String> usedNames = this.getUsedNames();

		if (!usedNames.contains(suggestedName)) {
			return suggestedName;
		}

		return generateWithCounter(suggestedName, usedNames);
	}

	private String generateWithCounter(String suggestedName, Set<String> usedNames) {

		int counter = 2;

		while (usedNames.contains(suggestedName + counter)) {
			++counter;
		}

		return suggestedName + counter;
	}

	private Set<String> getUsedNames() {

		Set<String> usedNames = SetFactory.createTreeSet();

		for (DeltaModule deltaModule: this.program.getDeltaModules()) {

			usedNames.add(deltaModule.getName());
		}

		return usedNames;
	}
}
