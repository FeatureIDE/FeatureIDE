package br.ufal.ic.colligens.actions;

import org.eclipse.jface.action.IAction;
import org.eclipse.ltk.ui.refactoring.RefactoringWizard;
import org.eclipse.ltk.ui.refactoring.RefactoringWizardOpenOperation;
import org.eclipse.swt.widgets.Shell;

import br.ufal.ic.colligens.controllers.refactoring.RefactoringController;
import br.ufal.ic.colligens.controllers.refactoring.RefactoringDataWizard;

public class RefactoringAction extends PluginActions {
	private final String WIZARD_NAME = "Refactoring";

	@Override
	public void run(IAction action) {
		RefactoringController refactoringController = new RefactoringController();
		refactoringController.setSelection(super.selection);
		run(new RefactoringDataWizard(refactoringController, WIZARD_NAME), super.window.getShell(),
				WIZARD_NAME);
	}

	public void run(RefactoringWizard wizard, Shell parent, String dialogTitle) {
		try {
			RefactoringWizardOpenOperation operation = new RefactoringWizardOpenOperation(
					wizard);
			operation.run(parent, dialogTitle);
		} catch (InterruptedException exception) {
			// Do nothing
		}
	}

}
