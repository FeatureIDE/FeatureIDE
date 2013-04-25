package org.deltaj.transformations.actions.finder;

import java.util.Collections;
import java.util.List;
import org.deltaj.deltaj.ClassAddition;
import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.DeltaAction;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.DeltaSubAction;
import org.deltaj.deltaj.Field;
import org.deltaj.deltaj.Method;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.deltaj.Program;
import org.deltaj.transformations.actions.DeltaJActionFactory;
import org.deltaj.transformations.actions.IDeltaJAction;
import org.deltaj.transformations.actions.IDeltaJClassAction;
import org.deltaj.transformations.finder.DeltaJModulesFinder;
import org.deltaj.transformations.utils.ListFactory;

/**
 * Searches through a DeltaJ program and returns all matching delta actions.
 * <p>
 * This is the abstract base class of all other action finders.
 * 
 * @author Oliver Richers
 */
abstract class AbstractActionFinder {

	private final List<IDeltaJAction> actions;

	public AbstractActionFinder() {

		this.actions = ListFactory.createArrayList();
	}

	public List<IDeltaJAction> find(Program program) {

		this.actions.clear();

		for (DeltaModule deltaModule: program.getDeltaModules()) {
			this.findInModule(deltaModule);
		}

		return Collections.unmodifiableList(actions);
	}

	public List<IDeltaJAction> find(ProductLine productLine) {

		this.actions.clear();

		for (DeltaModule deltaModule: new DeltaJModulesFinder().find(productLine)) {
			this.findInModule(deltaModule);
		}

		return Collections.unmodifiableList(actions);
	}

	public List<IDeltaJAction> find(DeltaModule deltaModule) {

		this.actions.clear();

		this.findInModule(deltaModule);

		return Collections.unmodifiableList(actions);
	}

	private void findInModule(DeltaModule deltaModule) {

		for (DeltaAction actionStatement: deltaModule.getDeltaActions()) {

			IDeltaJClassAction action = DeltaJActionFactory.get(actionStatement);
			addActionIfMatches(action);

			find(action);
		}
	}

	private void find(IDeltaJClassAction action) {

		switch (action.getActionType()) {
		case ADDITION:
			findImplicitAdditions(action);
			break;
		case MODIFICATION:
			findSubModifications(action);
			break;
		case REMOVAL:
			// nothing to do for class removals
			break;
		}
	}

	private void findImplicitAdditions(IDeltaJClassAction classAddition) {

		ClassAddition additionStatement = (ClassAddition) classAddition.getActionStatement();

		for (Method method: additionStatement.getClass_().getMethods()) {

			IDeltaJAction action = DeltaJActionFactory.get(classAddition, method);
			addActionIfMatches(action);
		}

		for (Field field: additionStatement.getClass_().getFields()) {

			IDeltaJAction action = DeltaJActionFactory.get(classAddition, field);
			addActionIfMatches(action);
		}
	}

	private void findSubModifications(IDeltaJClassAction classModification) {

		ClassModification modificationStatement = (ClassModification) classModification.getActionStatement();

		for (DeltaSubAction actionStatement: modificationStatement.getSubActions()) {

			IDeltaJAction action = DeltaJActionFactory.get(actionStatement);
			addActionIfMatches(action);
		}
	}

	private void addActionIfMatches(IDeltaJAction action) {

		if (matches(action)) {
			this.actions.add(action);
		}
	}

	protected abstract boolean matches(IDeltaJAction action);
}
