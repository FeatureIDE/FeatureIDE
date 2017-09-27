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
import br.ufal.ic.colligens.controllers.CoreController;
import br.ufal.ic.colligens.controllers.invalidconfigurations.InvalidConfigurationsViewController;
import br.ufal.ic.colligens.views.InvalidConfigurationsView;

public class CodeAnalyzeHandler extends ColligensAbstractHandler {

	private CoreController controller;

	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {

		final IWorkbenchWindow window = HandlerUtil.getActiveWorkbenchWindow(event);

		final ISelection selection = window.getActivePage().getSelection();

		if (selection != null) {
			if (controller == null) {
				controller = new CoreController();
			}

			controller.setWindow(HandlerUtil.getActiveWorkbenchWindow(event));
			controller.setSelection(selection);

			if (super.saveAll()) {
				final IWorkbenchPage page = window.getActivePage();
				try {

					page.showView(InvalidConfigurationsView.ID);
					final InvalidConfigurationsViewController analyzerViewController = InvalidConfigurationsViewController.getInstance();

					analyzerViewController.clear();

				} catch (final PartInitException e) {
					e.printStackTrace();
				}

				controller.run();
			} else {
				MessageDialog.openError(window.getShell(), Colligens.PLUGIN_NAME, PLEASE_SAVE_ALL_FILES_BEFORE_PROCEEDING_);
			}

		}

		return null;
	}
}
