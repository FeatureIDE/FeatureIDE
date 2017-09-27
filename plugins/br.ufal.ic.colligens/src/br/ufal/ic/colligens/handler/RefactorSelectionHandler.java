/**
 *
 */
package br.ufal.ic.colligens.handler;

import static de.ovgu.featureide.fm.core.localization.StringTable.REFACTORING___COLLIGENS;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IFile;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ltk.ui.refactoring.RefactoringWizardOpenOperation;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.ITextEditor;

import br.ufal.ic.colligens.controllers.refactoring.RefactorDataWizard;
import br.ufal.ic.colligens.controllers.refactoring.RefactorSelectionController;
import core.RefactoringType;

/**
 * @author Thiago Emmanuel
 *
 */
public class RefactorSelectionHandler extends ColligensAbstractHandler {

	public static String PARM_ID = "br.ufal.ic.colligens.RefactorParameter";
	public static String COMMAND_ID = "br.ufal.ic.colligens.commands.RefactorCommand";
	private final String WIZARD_NAME = REFACTORING___COLLIGENS;

	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {

		if (event.getParameter(RefactorSelectionHandler.PARM_ID) != null) {
			final IWorkbenchWindow window = HandlerUtil.getActiveWorkbenchWindow(event);

			run(window, event.getParameter(RefactorSelectionHandler.PARM_ID));

		}

		return null;
	}

	private void run(IWorkbenchWindow window, String type) {

		final RefactoringType refactoringType = RefactoringType.valueOf(type);

		ISelection selection = null;
		selection = window.getActivePage().getSelection();

		if (selection instanceof TextSelection) {

			final TextSelection textSelection = (TextSelection) selection;

			final Shell shell = window.getShell();

			final RefactorSelectionController refactoringController = new RefactorSelectionController();

			final FileEditorInput fileEditorInput = (FileEditorInput) window.getActivePage().getActiveEditor().getEditorInput();

			final IFile file = fileEditorInput.getFile();

			refactoringController.setSelection(file, textSelection, refactoringType);

			final RefactorDataWizard wizard = new RefactorDataWizard(refactoringController, WIZARD_NAME);
			try {
				final RefactoringWizardOpenOperation operation = new RefactoringWizardOpenOperation(wizard);
				operation.run(shell, WIZARD_NAME);
			} catch (final InterruptedException exception) {
				// Do nothing
			} catch (final NullPointerException exception) {
				// Do nothing
			}
		}
	}

	@Override
	public boolean isEnabled() {
		TextSelection textSelection = null;
		IEditorPart editorPart = null;
		try {
			editorPart = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor();
		} catch (final NullPointerException e) {
			return false;
		}

		if (editorPart instanceof ITextEditor) {
			if (super.isEnabled()) {

				final ITextEditor editor = (ITextEditor) editorPart;
				textSelection = (TextSelection) editor.getSelectionProvider().getSelection();

				final String line = textSelection.getText();
				if (line.contains("#")) {
					if (line.contains("#if ") || line.contains("#elif ") || line.contains("#ifdef ") || line.contains("#ifndef ") || line.contains("#else")) {

						return true;
					}

				}
			}
		}
		return false;

	}

}
