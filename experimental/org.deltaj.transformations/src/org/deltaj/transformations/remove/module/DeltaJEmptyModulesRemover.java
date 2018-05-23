package org.deltaj.transformations.remove.module;

import java.util.Set;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.PartitionPart;
import org.deltaj.deltaj.DeltaPartition;
import org.deltaj.deltaj.Program;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.transformations.evolution.DeltaJModuleRemover;
import org.deltaj.transformations.utils.SetFactory;

public class DeltaJEmptyModulesRemover {

	private final Set<DeltaModule> deltaModules = SetFactory.createIdentityHashSet();

	public DeltaJEmptyModulesRemover(Program program) {

		deltaModules.addAll(program.getDeltaModules());
	}

	public DeltaJEmptyModulesRemover(ProductLine productLine) {

		this(productLine.getPartition());
	}

	public DeltaJEmptyModulesRemover(DeltaPartition partition) {

		for (PartitionPart partitionPart: partition.getParts()) {
			addAll(partitionPart);
		}
	}

	public DeltaJEmptyModulesRemover(PartitionPart partitionPart) {

		addAll(partitionPart);
	}

	private void addAll(PartitionPart partitionPart) {

		for (ModuleReference moduleReference: partitionPart.getModuleReferences()) {
			deltaModules.add(moduleReference.getDeltaModule());
		}
	}

	public void remove() {

		for (DeltaModule deltaModule: deltaModules) {
			removeIfEmpty(deltaModule);
		}
	}

	private void removeIfEmpty(DeltaModule deltaModule) {

		if (deltaModule.getDeltaActions().isEmpty()) {
			new DeltaJModuleRemover(deltaModule).remove();
		}
	}
}
