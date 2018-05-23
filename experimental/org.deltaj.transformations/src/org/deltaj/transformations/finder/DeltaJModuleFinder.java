package org.deltaj.transformations.finder;

import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.Program;
import org.deltaj.transformations.finder.utils.AbstractFinder;

/**
 * Searches through a {@link Program} to find a delta module with the specified
 * name.
 * 
 * @author Oliver Richers
 */
public class DeltaJModuleFinder extends AbstractFinder<DeltaModule> {

	private final Program program;
	private final String moduleName;

	/**
	 * Constructs this finder.
	 * 
	 * @param program
	 *            the program to search in
	 * @param moduleName
	 *            the name of the delta module
	 */
	public DeltaJModuleFinder(Program program, String moduleName) {

		this.program = program;
		this.moduleName = moduleName;
	}

	/**
	 * Returns the delta module with the given name or null if no such module
	 * exists.
	 */
	@Override
	public DeltaModule find() {

		for (DeltaModule deltaModule: program.getDeltaModules()) {
			if (deltaModule.getName().equals(moduleName)) {
				return deltaModule;
			}
		}

		return null;
	}
}
