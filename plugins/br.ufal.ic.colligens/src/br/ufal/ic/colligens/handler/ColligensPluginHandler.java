package br.ufal.ic.colligens.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.handlers.HandlerUtil;

import br.ufal.ic.colligens.controllers.CoreController;
import br.ufal.ic.colligens.controllers.invalidconfigurations.InvalidConfigurationsViewController;
import br.ufal.ic.colligens.views.InvalidConfigurationsView;

public class ColligensPluginHandler extends AbstractHandler {
	private IWorkbenchWindow window;
	private CoreController controller;

	/**
	 * the command has been executed, so extract extract the needed information
	 * from the application context.
	 */
	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		this.window = HandlerUtil.getActiveWorkbenchWindow(event);

		if (controller == null) {
			controller = new CoreController();
		}

		controller.setWindow(window);
		// Open and active the Analyzer view
		IWorkbenchPage page = window.getActivePage();
		try {
			page.showView(InvalidConfigurationsView.ID);
			InvalidConfigurationsViewController analyzerViewController = InvalidConfigurationsViewController
					.getInstance();

			analyzerViewController.clear();
		} catch (PartInitException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		controller.run();

		return null;
	}

}
