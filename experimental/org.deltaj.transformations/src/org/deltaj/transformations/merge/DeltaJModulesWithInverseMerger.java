package org.deltaj.transformations.merge;

import java.util.Map;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.transformations.actions.IDeltaJAction;
import org.deltaj.transformations.actions.finder.DeltaJActionFinder;
import org.deltaj.transformations.finder.DeltaJModuleReferenceFinder;
import org.deltaj.transformations.formula.DeltaJFormulaBuilder;
import org.deltaj.transformations.modules.references.DeltaJModuleReference;
import org.deltaj.transformations.rename.DeltaJModuleRenamer;
import org.deltaj.transformations.utils.MapFactory;
import org.deltaj.transformations.utils.exceptions.DeltaJException;
import org.deltaj.transformations.utils.logical.LogicalActionsApplier;

public class DeltaJModulesWithInverseMerger {

	private final DeltaJModuleReference moduleReferenceA;
	private final DeltaJModuleReference moduleReferenceB;
	private final Map<String, IDeltaJAction> actionsA;
	private final Map<String, IDeltaJAction> actionsB;

	public DeltaJModulesWithInverseMerger(DeltaModule deltaModuleA, DeltaModule deltaModuleB) {

		this(findReference(deltaModuleA), findReference(deltaModuleB));
	}

	private static DeltaJModuleReference findReference(DeltaModule deltaModuleA) {

		return new DeltaJModuleReferenceFinder(deltaModuleA).findExactlyOne();
	}

	public DeltaJModulesWithInverseMerger(DeltaJModuleReference moduleReferenceA, DeltaJModuleReference moduleReferenceB) {

		this.moduleReferenceA = moduleReferenceA;
		this.moduleReferenceB = moduleReferenceB;
		this.actionsA = findActions(moduleReferenceA.getDeltaModule());
		this.actionsB = findActions(moduleReferenceB.getDeltaModule());

		validateModuleOrder();
		validateActionsOfFirstModule();
		validateActionsOfSecondModule();
	}

	public void merge() {

		DeltaModule deltaModuleA = moduleReferenceA.getDeltaModule();
		DeltaModule deltaModuleB = moduleReferenceB.getDeltaModule();

		// merge
		new LogicalActionsApplier(deltaModuleA, deltaModuleB).apply();

		// change application conditions
		DeltaJFormulaBuilder builder = new DeltaJFormulaBuilder();
		PropositionalFormula conditionA = builder.copy(moduleReferenceA.getApplicationCondition());
		PropositionalFormula conditionB = builder.copy(moduleReferenceB.getApplicationCondition());
		PropositionalFormula newConditionB = builder.and(conditionA, builder.not(conditionB));

		moduleReferenceB.getStatement().setWhen(newConditionB);

		// rename modules
		String nameA = deltaModuleA.getName();
		String nameB = deltaModuleB.getName();
		new DeltaJModuleRenamer(deltaModuleA, nameA + nameB).rename();
		new DeltaJModuleRenamer(deltaModuleB, nameB + "Inverse").rename();
	}

	private Map<String, IDeltaJAction> findActions(DeltaModule deltaModule) {

		Map<String, IDeltaJAction> actions = MapFactory.createTreeMap();

		for (IDeltaJAction action: new DeltaJActionFinder().find(deltaModule)) {
			IDeltaJAction previous = actions.put(action.getTargetName(), action);
			if (previous != null) {
				throw new DeltaJException(
						"The target '%s' was modified twice in delta module '%s'.",
						action.getTargetName(),
						deltaModule.getName());
			}
		}

		return actions;
	}

	private void validateModuleOrder() {

		int partitionDistance = moduleReferenceB.getPartitionOrder() - moduleReferenceA.getPartitionOrder();
		if (partitionDistance < 0 || partitionDistance > 1) {
			throw new DeltaJException("Delta modules must be in the same of two consecutive partition parts.");
		}
	}

	private void validateActionsOfFirstModule() {

		for (IDeltaJAction action: actionsA.values()) {
			switch (action.getActionType()) {
			case ADDITION:
				break; // all additions are okay
			case MODIFICATION:
				switch (action.getTargetType()) {
				case CLASS:
					break; // class modifications are okay
				case METHOD:
				case FIELD:
					throw new DeltaJException(
							"The method or field modification action for '%s' is not allowed in delta module '%s'.",
							action.getTargetName(),
							moduleReferenceA.getDeltaModule().getName());
				}
				break;
			case REMOVAL:
				throw new DeltaJException(
						"The removal action for '%s' is not allowed in delta module '%s'.",
						action.getTargetName(),
						moduleReferenceA.getDeltaModule().getName());
			}
		}
	}

	private void validateActionsOfSecondModule() {

		for (IDeltaJAction action: actionsB.values()) {
			switch (action.getActionType()) {
			case ADDITION:
				break; // all additions are okay
			case MODIFICATION:
				switch (action.getTargetType()) {
				case CLASS:
					break; // class modifications are okay
				case METHOD:
				case FIELD:
					if (!actionsA.containsKey(action.getTargetName())) {
						throw new DeltaJException(
								"The field or method modification action for '%s' is not allowed in delta module '%s', because '%s' does not contain a corresponding addition or modification action.",
								action.getTargetName(),
								moduleReferenceB.getDeltaModule().getName(),
								moduleReferenceA.getDeltaModule().getName());
					}
					break;
				}
				break;
			case REMOVAL:
				if (!actionsA.containsKey(action.getTargetName())) {
					throw new DeltaJException(
							"The removal action for '%s' is not allowed in delta module '%s', because '%s' does not contain a corresponding addition or modification action.",
							action.getTargetName(),
							moduleReferenceB.getDeltaModule().getName(),
							moduleReferenceA.getDeltaModule().getName());
				}
				break;
			}
		}
	}
}
