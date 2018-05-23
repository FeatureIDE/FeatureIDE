package org.deltaj.transformations.evolution;

import java.util.Collection;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.PartitionPart;
import org.deltaj.deltaj.DeltaPartition;
import org.deltaj.transformations.finder.DeltaJModuleReferenceFinder;
import org.deltaj.transformations.modules.references.DeltaJModuleReference;

/**
 * Checks the validity of a delta module removal.
 * <p>
 * Currently, it is only checked that the removed delta module is not the last
 * existing module. Because a DeltaJ has to contain at least one delta module.
 * 
 * @author Oliver Richers
 */
class DeltaJModuleRemovalValidator {

	private final DeltaModule deltaModule;

	public DeltaJModuleRemovalValidator(DeltaModule deltaModule) {

		this.deltaModule = deltaModule;
	}

	public void validate() {

		Collection<DeltaJModuleReference> moduleReferences = new DeltaJModuleReferenceFinder(this.deltaModule)
				.findMap()
				.values();

		for (DeltaJModuleReference moduleReference: moduleReferences) {
			DeltaPartition partition = moduleReference.getPartition();
			if (partition.getParts().size() == 1) {

				PartitionPart partitionPart = partition.getParts().get(0);
				if (partitionPart.getModuleReferences().size() == 1) {

					ModuleReference referenceStatement = partitionPart.getModuleReferences().get(0);
					if (referenceStatement == moduleReference.getStatement()) {
						throw new DeltaJModuleRemovalException(
								"Cannot remove delta module '%s', because it is the last delta module in the product line '%s'.",
								this.deltaModule.getName(),
								moduleReference.getSplName());
					}
				}
			}
		}
	}
}
