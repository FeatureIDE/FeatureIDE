package org.deltaj.transformations.extract;

import org.deltaj.deltaj.DeltaAction;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.FeatureRef;
import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.DeltaSubAction;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.Program;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.transformations.actions.DeltaJActionFactory;
import org.deltaj.transformations.actions.DeltaJActionTargetType;
import org.deltaj.transformations.actions.IDeltaJAction;
import org.deltaj.transformations.actions.IDeltaJClassAction;
import org.deltaj.transformations.exceptions.DeltaJIllegalEnumConstant;
import org.deltaj.transformations.formula.DeltaJFormulaCopier;
import org.deltaj.transformations.modules.references.DeltaJModuleReference;
import org.deltaj.transformations.names.DeltaJModuleNameGenerator;

public class DeltaJActionExtractor {

	private final DeltajFactory factory;
	private final IDeltaJAction action;
	private final DeltaModule originalDeltaModule;
	private final Program program;
	private DeltaModule newDeltaModule;

	public DeltaJActionExtractor(DeltaAction action) {

		this(DeltaJActionFactory.get(action));
	}

	public DeltaJActionExtractor(DeltaSubAction action) {

		this(DeltaJActionFactory.get(action));
	}

	public DeltaJActionExtractor(IDeltaJAction action) {

		this.factory = DeltajFactory.eINSTANCE;
		this.action = action;
		this.originalDeltaModule = this.action.getDeltaModule();
		this.program = action.getProgram();
	}

	public DeltaModule extract() {

		createNewDeltaModule();

		for (DeltaJModuleReference moduleReference: action.findModuleReferences().values()) {

			transform(moduleReference);
		}

		new ActionMover(newDeltaModule).move(action);

		return newDeltaModule;
	}

	public DeltaModule extractIfNecessary() {

		DeltaModule deltaModule = action.getDeltaModule();

		if (isExtractionNecessary(deltaModule)) {
			return extract();
		} else {
			return deltaModule;
		}
	}

	private boolean isExtractionNecessary(DeltaModule deltaModule) {

		DeltaJActionTargetType targetType = action.getTargetType();

		switch (targetType) {
		case CLASS:
			return deltaModule.getDeltaActions().size() > 1;
		case METHOD:
		case FIELD:
			IDeltaJClassAction parentAction = action.getParentAction();

			switch (parentAction.getActionType()) {
			case ADDITION:
				return true;
			case MODIFICATION:
				ClassModification modifiesClass = (ClassModification) parentAction.getActionStatement();
				return modifiesClass.getSubActions().size() > 1;
			default:
				throw new DeltaJIllegalEnumConstant(targetType);
			}
		default:
			throw new DeltaJIllegalEnumConstant(targetType);
		}
	}

	private void createNewDeltaModule() {

		newDeltaModule = factory.createDeltaModule();
		newDeltaModule.setName(generateModuleName());
		action.getProgram().getDeltaModules().add(newDeltaModule);
	}

	private String generateModuleName() {

		String suggestedName = originalDeltaModule.getName() + "_" + action.getTargetName().replace('.', '_');
		return new DeltaJModuleNameGenerator(program).generate(suggestedName);
	}

	private void transform(DeltaJModuleReference originalModuleReference) {

		FeatureRef featureRef = factory.createFeatureRef();
		featureRef.setFeature(originalModuleReference.getSplSpecification().getFeatures().getFeaturesList().get(0));

		// create reference statement
		ModuleReference referenceStatement = factory.createModuleReference();
		referenceStatement.setDeltaModule(newDeltaModule);
		referenceStatement.setWhen(copyFormula(originalModuleReference));

		// add to partition part
		originalModuleReference.getPartitionPart().getModuleReferences().add(referenceStatement);
	}

	private PropositionalFormula copyFormula(DeltaJModuleReference originalModuleReference) {

		PropositionalFormula formula = originalModuleReference.getStatement().getWhen();

		return new DeltaJFormulaCopier().copy(formula);
	}
}
