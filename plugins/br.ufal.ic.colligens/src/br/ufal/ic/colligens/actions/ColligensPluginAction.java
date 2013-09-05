package br.ufal.ic.colligens.actions;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;

import br.ufal.ic.colligens.activator.Colligens;
import br.ufal.ic.colligens.controllers.CoreController;
import br.ufal.ic.colligens.controllers.invalidconfigurations.InvalidConfigurationsViewController;
import br.ufal.ic.colligens.views.InvalidConfigurationsView;

public class ColligensPluginAction extends PluginActions {
	private CoreController controller;

	@Override
	public void run(IAction action) {

		if (controller == null) {
			controller = new CoreController();
		}

		controller.setWindow(super.window);

		if (saveAll()) {
			IWorkbenchPage page = super.window.getActivePage();
			try {

				page.showView(InvalidConfigurationsView.ID);
				InvalidConfigurationsViewController analyzerViewController = InvalidConfigurationsViewController
						.getInstance();

				analyzerViewController.clear();

			} catch (PartInitException e) {
				e.printStackTrace();
			}

			controller.run();
		} else {
			MessageDialog.openError(window.getShell(), Colligens.PLUGIN_NAME,
					"Please save all files before proceeding.");
		}

	}
}
