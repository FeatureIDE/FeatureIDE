package org.deltaj.transformations.merge;

import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedMap;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.PartitionPart;
import org.deltaj.transformations.formula.DeltaJFormulaComparator;
import org.deltaj.transformations.merge.simple.DeltaJClassActionsOfModuleMerger;
import org.deltaj.transformations.utils.MapFactory;
import org.deltaj.transformations.utils.MapUtils;
import org.deltaj.transformations.utils.SetFactory;

/**
 * Analyzes the delta modules in the given partition part and merges them if
 * possible.
 * 
 * TODO: This only works if there is only one product line!!!
 * 
 * @author Oliver Richers
 */
public class DeltaJModulesWithEquivalentConditionsOfPartitionPartMerger {

	private final PartitionPart partitionPart;
	private final SortedMap<Integer, ModuleReference> deltaModules;
	private final Map<DeltaModule, List<DeltaModule>> equivalentModules;

	public DeltaJModulesWithEquivalentConditionsOfPartitionPartMerger(PartitionPart partitionPart) {

		this.partitionPart = partitionPart;
		this.deltaModules = MapFactory.createTreeMap();
		this.equivalentModules = MapFactory.createIdentityHashMap();
	}

	public void merge() {

		fetchDeltaModules();
		findModulesWithEquivalentConditions();
		mergeModulesWithEquivalentConditions();
	}

	private void fetchDeltaModules() {

		int index = 0;
		for (ModuleReference moduleReference: partitionPart.getModuleReferences()) {
			deltaModules.put(index, moduleReference);
			++index;
		}
	}

	private void findModulesWithEquivalentConditions() {

		while (!deltaModules.isEmpty()) {

			// take the first delta module
			ModuleReference firstModule = MapUtils.removeFirstValue(deltaModules);

			// find subsequent delta modules
			for (int indexOfMatchingModule: findModulesWithEquivalentConditions(firstModule)) {

				ModuleReference matchingModule = deltaModules.remove(indexOfMatchingModule);
				MapUtils.addToListMap(equivalentModules, firstModule.getDeltaModule(), matchingModule.getDeltaModule());
			}
		}
	}

	private Set<Integer> findModulesWithEquivalentConditions(ModuleReference deltaModule) {

		Set<Integer> matchingModules = SetFactory.createTreeSet();

		for (Entry<Integer, ModuleReference> subsequentModule: deltaModules.entrySet()) {

			if (haveEqualConditions(deltaModule, subsequentModule.getValue())) {
				matchingModules.add(subsequentModule.getKey());
			}
		}

		return matchingModules;
	}

	private boolean haveEqualConditions(ModuleReference moduleReferenceA, ModuleReference moduleReferenceB) {

		return new DeltaJFormulaComparator(moduleReferenceA.getWhen(), moduleReferenceB.getWhen()).isEqual();
	}

	private void mergeModulesWithEquivalentConditions() {

		for (Entry<DeltaModule, List<DeltaModule>> entry: equivalentModules.entrySet()) {

			DeltaModule deltaModuleA = entry.getKey();
			mergeModules(deltaModuleA, entry.getValue());
		}
	}

	private void mergeModules(DeltaModule deltaModuleA, List<DeltaModule> deltaModulesB) {

		for (DeltaModule deltaModuleB: deltaModulesB) {

			new DeltaJModulesWithEquivalentConditionsMerger(deltaModuleA, deltaModuleB).merge();
		}

		new DeltaJClassActionsOfModuleMerger(deltaModuleA).merge();
	}
}
