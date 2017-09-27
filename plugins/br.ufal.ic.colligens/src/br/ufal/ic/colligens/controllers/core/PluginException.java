package br.ufal.ic.colligens.controllers.core;

import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;

import br.ufal.ic.colligens.activator.Colligens;
import br.ufal.ic.colligens.controllers.CoreController;

public class PluginException extends Exception {

	/**
	 *
	 */
	private static final long serialVersionUID = 1L;

	public PluginException(final String message) {
		super(message);
		Display.getDefault().asyncExec(new Runnable() {

			@Override
			public void run() {
				Shell shell;
				if (CoreController.getWindow() != null) {
					shell = CoreController.getWindow().getShell();
				} else {
					shell = new Shell();
				}
				MessageDialog.openError(shell, Colligens.PLUGIN_NAME, message);
			}
		});
	}
}
