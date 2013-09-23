package br.ufal.ic.colligens.actions.popup;

import java.util.Iterator;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.ltk.ui.refactoring.RefactoringWizard;
import org.eclipse.ltk.ui.refactoring.RefactoringWizardOpenOperation;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.ITextEditor;

import br.ufal.ic.colligens.controllers.refactoring.RefactoringDataWizard;
import br.ufal.ic.colligens.controllers.refactoring.RefactoringSelectionController;

public class RefactorSelectionAction implements IObjectActionDelegate {
	private final String WIZARD_NAME = "Refactoring - Colligens";
	private TextSelection textSelection = null;
	private IFile file = null;
	private Shell shell;

	/**
	 * Constructor for Action1.
	 */
	public RefactorSelectionAction() {
		super();
	}

	/**
	 * @see IObjectActionDelegate#setActivePart(IAction, IWorkbenchPart)
	 */
	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
		shell = targetPart.getSite().getShell();
	}

	/**
	 * @see IActionDelegate#run(IAction)
	 */
	@Override
	public void run(IAction action) {
		RefactoringSelectionController refactoringController = new RefactoringSelectionController();
		refactoringController.setSelection(file, textSelection);
		run(new RefactoringDataWizard(refactoringController, WIZARD_NAME),
				shell);
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

	/**
	 * @see IActionDelegate#selectionChanged(IAction, ISelection)
	 */
	public void selectionChanged(IAction action, ISelection selection) {
		action.setEnabled(false);

		IEditorPart part = PlatformUI.getWorkbench().getActiveWorkbenchWindow()
				.getActivePage().getActiveEditor();

		if (part instanceof ITextEditor) {
			ITextEditor editor = (ITextEditor) part;
			this.textSelection = (TextSelection) editor
					.getSelectionProvider().getSelection();

			String line = textSelection.getText();
			if (line.contains("#")) {
				if (line.contains("#if ") || line.contains("#elif ")
						|| line.contains("#ifdef ")
						|| line.contains("#ifndef ") || line.contains("#else")) {

					if (selection instanceof StructuredSelection) {
						StructuredSelection structuredSelection = (StructuredSelection) selection;

						for (Iterator<?> iterator = structuredSelection
								.iterator(); iterator.hasNext();) {
							Object object = (Object) iterator.next();

							if (object instanceof FileEditorInput) {
								FileEditorInput editorInput = (FileEditorInput) object;
								this.file = editorInput.getFile();
								action.setEnabled(this.file != null);
							}
						}
					}
				}

			}
		}
	}

}
