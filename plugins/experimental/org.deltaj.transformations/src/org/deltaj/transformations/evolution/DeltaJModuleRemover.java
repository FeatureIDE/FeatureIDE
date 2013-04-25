package org.deltaj.transformations.evolution;

import java.util.Collection;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.PartitionPart;
import org.deltaj.deltaj.DeltaPartition;
import org.deltaj.deltaj.Program;
import org.deltaj.transformations.finder.DeltaJModuleFinder;
import org.deltaj.transformations.finder.DeltaJModuleReferenceFinder;
import org.deltaj.transformations.modules.references.DeltaJModuleReference;
import org.deltaj.transformations.utils.GrammarUtils;
import org.deltaj.transformations.utils.ListUtils;

/**
 * Removes a delta module and all its references from a DeltaJ program.
 * 
 * @author Oliver Richers
 */
public class DeltaJModuleRemover {

	private final DeltaModule deltaModule;

	public DeltaJModuleRemover(Program program, String moduleName) {

		this.deltaModule = new DeltaJModuleFinder(program, moduleName).findOrThrow();
	}

	public DeltaJModuleRemover(DeltaModule deltaModule) {

		this.deltaModule = deltaModule;
	}

	public void remove() {

		this.checkValidity();

		this.removeReferences();

		this.removeDefinition();
	}

	private void checkValidity() {

		new DeltaJModuleRemovalValidator(this.deltaModule).validate();
	}

	private void removeDefinition() {

		Program program = GrammarUtils.getProgram(this.deltaModule);

		ListUtils.removeElementByIdentity(program.getDeltaModules(), this.deltaModule);
	}

	private void removeReferences() {

		Collection<DeltaJModuleReference> moduleReferences = new DeltaJModuleReferenceFinder(this.deltaModule)
				.findMap()
				.values();

		for (DeltaJModuleReference moduleReference: moduleReferences) {

			this.removeReference(moduleReference);
		}
	}

	private void removeReference(DeltaJModuleReference moduleReference) {

		PartitionPart partitionPart = moduleReference.getPartitionPart();
		ModuleReference referenceStatement = moduleReference.getStatement();

		ListUtils.removeElementByIdentity(partitionPart.getModuleReferences(), referenceStatement);

		if (partitionPart.getModuleReferences().isEmpty()) {
			this.removePartitionPart(partitionPart);
		}
	}

	private void removePartitionPart(PartitionPart partitionPart) {

		DeltaPartition partition = GrammarUtils.getPartition(partitionPart);

		ListUtils.removeElementByIdentity(partition.getParts(), partitionPart);
	}
}
