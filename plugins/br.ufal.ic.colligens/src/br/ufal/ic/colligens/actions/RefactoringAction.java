package br.ufal.ic.colligens.actions;

import org.eclipse.jface.action.IAction;
import org.eclipse.ltk.ui.refactoring.RefactoringWizard;
import org.eclipse.ltk.ui.refactoring.RefactoringWizardOpenOperation;
import org.eclipse.swt.widgets.Shell;

import br.ufal.ic.colligens.controllers.refactoring.RefactoringFileController;
import br.ufal.ic.colligens.controllers.refactoring.RefactoringDataWizard;

public class RefactoringAction extends PluginActions {
	private final String WIZARD_NAME = "Refactoring - Colligens";

	@Override
	public void run(IAction action) {
		RefactoringFileController refactoringController = new RefactoringFileController();
		refactoringController.setSelection(super.selection);
		run(new RefactoringDataWizard(refactoringController, WIZARD_NAME), super.window.getShell());
	}

	public void run(RefactoringWizard wizard, Shell parent) {
		try {
			RefactoringWizardOpenOperation operation = new RefactoringWizardOpenOperation(
					wizard);
			operation.run(parent, WIZARD_NAME);
		} catch (InterruptedException exception) {
			// Do nothing
		}
	}

}
