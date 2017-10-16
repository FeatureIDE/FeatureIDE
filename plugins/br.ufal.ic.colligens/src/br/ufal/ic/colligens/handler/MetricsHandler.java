/**
 *
 */
package br.ufal.ic.colligens.handler;

import static de.ovgu.featureide.fm.core.localization.StringTable.PLEASE_SAVE_ALL_FILES_BEFORE_PROCEEDING_;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.handlers.HandlerUtil;

import br.ufal.ic.colligens.activator.Colligens;
import br.ufal.ic.colligens.controllers.MetricsController;
import br.ufal.ic.colligens.views.MetricsView;

/**
 * @author Thiago Emmanuel
 *
 */
public class MetricsHandler extends ColligensAbstractHandler {

	private MetricsController controller;

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands. ExecutionEvent)
	 */
	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		final IWorkbenchWindow window = HandlerUtil.getActiveWorkbenchWindow(event);

		final ISelection selection = window.getActivePage().getSelection();

		if (controller == null) {
			controller = new MetricsController();
		}

		controller.setWindow(window);
		controller.setSelection(selection);

		if (super.saveAll()) {
			// Open and active the Analyzer view
			final IWorkbenchPage page = window.getActivePage();
			try {
				page.showView(MetricsView.ID);
			} catch (final PartInitException e) {

				e.printStackTrace();
			}
			controller.run();

		} else {
			MessageDialog.openError(window.getShell(), Colligens.PLUGIN_NAME, PLEASE_SAVE_ALL_FILES_BEFORE_PROCEEDING_);
		}
		return null;
	}

}
