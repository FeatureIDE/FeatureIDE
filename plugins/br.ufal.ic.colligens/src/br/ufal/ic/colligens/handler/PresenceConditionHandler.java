/**
 *
 */
package br.ufal.ic.colligens.handler;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IFile;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.texteditor.ITextEditor;

import br.ufal.ic.colligens.controllers.PresenceConditionController;
import br.ufal.ic.colligens.controllers.core.PluginException;
import br.ufal.ic.colligens.controllers.invalidconfigurations.InvalidConfigurationsViewController;
import br.ufal.ic.colligens.models.FileProxy;
import br.ufal.ic.colligens.views.InvalidConfigurationsView;
import de.fosd.typechef.options.OptionException;

/**
 * @author thiago
 *
 */
public class PresenceConditionHandler extends ColligensAbstractHandler {

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands. ExecutionEvent)
	 */
	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		final IWorkbenchWindow window = HandlerUtil.getActiveWorkbenchWindow(event);
		final IWorkbenchPage page = window.getActivePage();
		final IEditorPart editor = page.getActiveEditor();

		if (editor instanceof ITextEditor) {

			final ISelectionProvider selectionProvider = ((ITextEditor) editor).getSelectionProvider();
			final ISelection selection = selectionProvider.getSelection();

			if (selection instanceof ITextSelection) {

				final TextSelection textSelection = (TextSelection) selection;

				final IDocumentProvider provider = ((ITextEditor) editor).getDocumentProvider();
				final IDocument document = provider.getDocument(editor.getEditorInput());
				final int line = textSelection.getStartLine();

				final FileEditorInput fileEditorInput = (FileEditorInput) window.getActivePage().getActiveEditor().getEditorInput();

				final IFile file = fileEditorInput.getFile();
				String code = null;
				try {
					code = document.get(document.getLineOffset(line), document.getLineLength(line));
				} catch (final BadLocationException e1) {

					e1.printStackTrace();
				}

				final PresenceConditionController conditionController = new PresenceConditionController(file, line + 1, code);

				try {
					conditionController.run();

					// show erros

					if ((conditionController.getFileProxy() != null) && !conditionController.getFileProxy().getLogs().isEmpty()) {
						try {
							page.showView(InvalidConfigurationsView.ID);
							final InvalidConfigurationsViewController analyzerViewController = InvalidConfigurationsViewController.getInstance();

							analyzerViewController.clear();

							final List<FileProxy> list = new LinkedList<FileProxy>();

							list.add(conditionController.getFileProxy());

							analyzerViewController.setInput(list);

						} catch (final PartInitException e) {
							e.printStackTrace();
						}
					}
					// ---
				} catch (final PluginException e) {
					e.printStackTrace();
				} catch (final OptionException e) {
					e.printStackTrace();
				} catch (final IOException e) {
					e.printStackTrace();
				}

			}
		}

		// -----------------

		return null;
	}
}
