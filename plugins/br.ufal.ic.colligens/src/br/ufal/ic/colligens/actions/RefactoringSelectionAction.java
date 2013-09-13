package br.ufal.ic.colligens.actions;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ltk.ui.refactoring.RefactoringWizard;
import org.eclipse.ltk.ui.refactoring.RefactoringWizardOpenOperation;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PlatformUI;

import br.ufal.ic.colligens.controllers.refactoring.RefactoringDataWizard;
import br.ufal.ic.colligens.controllers.refactoring.RefactoringSelectionController;

public class RefactoringSelectionAction extends PluginActions {
	private final String WIZARD_NAME = "Refactoring - Colligens";
	private TextSelection textSelection = null;
	private IFile file = null;

	@Override
	public void run(IAction action) {
		RefactoringSelectionController refactoringController = new RefactoringSelectionController();
		refactoringController.setSelection(file, textSelection);
		run(new RefactoringDataWizard(refactoringController, WIZARD_NAME),
				super.window.getShell());
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

	@Override
	public void selectionChanged(IAction action, ISelection selection) {
		action.setEnabled(false);
		if (selection instanceof TextSelection) {
			textSelection = (TextSelection) selection;
			String line = textSelection.getText();
			if (line.contains("#")) {
				if (line.contains("#if ") || line.contains("#elif ")
						|| line.contains("#ifdef ")
						|| line.contains("#ifndef ") || line.contains("#else")) {

					IWorkbenchPart workbenchPart = PlatformUI.getWorkbench()
							.getActiveWorkbenchWindow().getActivePage()
							.getActivePart();
					IFile file = (IFile) workbenchPart.getSite().getPage()
							.getActiveEditor().getEditorInput()
							.getAdapter(IFile.class);
					if (file != null) {
						this.file = file;
						action.setEnabled(true);
					}
				}
			}
		}
	}
}
