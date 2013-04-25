package org.deltaj.transformations.finder;

import java.util.Map;
import java.util.Set;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.PartitionPart;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.deltaj.Program;
import org.deltaj.transformations.modules.references.DeltaJModuleReference;
import org.deltaj.transformations.modules.references.DeltaJModuleReferenceImpl;
import org.deltaj.transformations.utils.DeltaJHierarchy;
import org.deltaj.transformations.utils.MapFactory;
import org.deltaj.transformations.utils.MapUtils;
import org.deltaj.transformations.utils.SetFactory;
import org.deltaj.transformations.utils.exceptions.DeltaJException;

public class DeltaJModuleReferenceFinder {

	private final Program program;
	private final DeltaModule deltaModule;

	public DeltaJModuleReferenceFinder(DeltaModule deltaModule) {

		this.program = DeltaJHierarchy.getProgram(deltaModule);
		this.deltaModule = deltaModule;
	}

	public DeltaJModuleReference find(String splName) {

		return findMap().get(splName);
	}

	public DeltaJModuleReference findOneOrNone() {

		Map<String, DeltaJModuleReference> referenceMap = findMap();

		if (referenceMap.size() > 1) {
			throw new DeltaJException("Found more that one reference to delta module '%s'.", deltaModule.getName());
		}

		return MapUtils.getFirstValue(referenceMap);
	}

	public DeltaJModuleReference findExactlyOne() {

		DeltaJModuleReference moduleReference = findOneOrNone();

		if (moduleReference == null) {
			throw new DeltaJException("Failed to find reference to delta module '%s'.", deltaModule.getName());
		}

		return moduleReference;
	}

	public Set<ModuleReference> find() {

		Set<ModuleReference> moduleReferences = SetFactory.createIdentityHashSet();

		for (DeltaJModuleReference moduleReference: findMap().values()) {

			moduleReferences.add(moduleReference.getStatement());
		}

		return moduleReferences;
	}

	public Map<String, DeltaJModuleReference> findMap() {

		Map<String, DeltaJModuleReference> splReferences = MapFactory.createTreeMap();

		for (ProductLine productLine: this.program.getProductLines()) {

			int partitionOrder = 0;

			for (PartitionPart partitionPart: productLine.getPartition().getParts()) {

				for (ModuleReference moduleReference: partitionPart.getModuleReferences()) {

					if (moduleReference.getDeltaModule() == this.deltaModule) {

						DeltaJModuleReference reference = DeltaJModuleReferenceImpl
								.get(moduleReference, partitionOrder);
						splReferences.put(reference.getSplName(), reference);
					}
				}

				++partitionOrder;
			}
		}

		return splReferences;
	}
}
