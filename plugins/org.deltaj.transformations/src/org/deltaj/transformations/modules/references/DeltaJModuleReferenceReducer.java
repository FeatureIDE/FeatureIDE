package org.deltaj.transformations.modules.references;

import java.util.Map;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.PartitionPart;
import org.deltaj.deltaj.DeltaPartition;
import org.deltaj.deltaj.PropFalse;
import org.deltaj.deltaj.PropTrue;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.transformations.evolution.DeltaJModuleRemover;
import org.deltaj.transformations.finder.DeltaJModuleReferenceFinder;
import org.deltaj.transformations.formula.DeltaJFormulaOptimizer;
import org.deltaj.transformations.utils.ListUtils;

/**
 * Reduces a given reference of a delta module.
 * <p>
 * First, the application condition of the module reference will be minimized.
 * If the resulting condition is a tautology, the condition will be removed from
 * the module reference completely. If the resulting condition is a
 * contradiction, the whole module reference will be removed and if there is no
 * other reference to the delta module, the module is also removed.
 * 
 * @author Oliver Richers
 */
public class DeltaJModuleReferenceReducer {

	private final DeltaJModuleReference moduleReference;

	public DeltaJModuleReferenceReducer(DeltaJModuleReference moduleReference) {

		this.moduleReference = moduleReference;
	}

	public void reduce() {

		PropositionalFormula formula = moduleReference.getApplicationCondition();

		if (formula != null) {
			formula = new DeltaJFormulaOptimizer(formula).optimize();

			if (formula instanceof PropTrue) {
				removeCondition();
			} else if (formula instanceof PropFalse) {
				removeReference();
			} else {
				replaceFormula(formula);
			}
		}
	}

	private void removeCondition() {

		moduleReference.getStatement().setWhen(null);
	}

	private void removeReference() {

		PartitionPart partitionPart = moduleReference.getPartitionPart();

		if (partitionPart.getModuleReferences().size() == 1) {
			removePartitionPart(partitionPart);
		} else {
			removeReference(partitionPart);
		}

		removeDeltaModuleIfUnused();
	}

	private void removeDeltaModuleIfUnused() {

		DeltaModule deltaModule = moduleReference.getStatement().getDeltaModule();
		Map<String, DeltaJModuleReference> references = new DeltaJModuleReferenceFinder(deltaModule).findMap();
		if (references.isEmpty()) {
			new DeltaJModuleRemover(deltaModule).remove();
		}
	}

	private void removePartitionPart(PartitionPart partitionPart) {

		assert partitionPart.getModuleReferences().get(0) == moduleReference.getStatement();
		DeltaPartition partition = moduleReference.getPartition();
		ListUtils.removeElementByIdentity(partition.getParts(), partitionPart);
	}

	private void removeReference(PartitionPart partitionPart) {

		ListUtils.removeElementByIdentity(partitionPart.getModuleReferences(), moduleReference.getStatement());
	}

	private void replaceFormula(PropositionalFormula formula) {

		moduleReference.getStatement().setWhen(formula);
	}
}
