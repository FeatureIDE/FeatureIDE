package br.ufal.ic.colligens.actions;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;

import br.ufal.ic.colligens.activator.Colligens;
import br.ufal.ic.colligens.controllers.MetricsController;
import br.ufal.ic.colligens.util.metrics.MetricsException;
import br.ufal.ic.colligens.views.MetricsView;

public class MetricsAction extends PluginActions {
	private MetricsController controller;

	@Override
	public void run(IAction action) {
		if (controller == null) {
			controller = new MetricsController();
		}

		controller.setWindow(super.window);

		// Open and active the Analyzer view
		IWorkbenchPage page = super.window.getActivePage();
		try {
			page.showView(MetricsView.ID);
		} catch (PartInitException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		try {
			if (saveAll()) {
				controller.run();
			} else {
				MessageDialog.openError(window.getShell(),
						Colligens.PLUGIN_NAME,
						"Please save all files before proceeding.");
			}
		} catch (MetricsException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

}
