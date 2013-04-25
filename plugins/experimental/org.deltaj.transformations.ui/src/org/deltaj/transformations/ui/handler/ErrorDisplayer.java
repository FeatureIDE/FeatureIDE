package org.deltaj.transformations.ui.handler;

import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;

public class ErrorDisplayer {

	private String title = "Error";

	public ErrorDisplayer setTitle(String text, Object...args) {

		this.title = String.format(text, args);
		return this;
	}

	public void showError(String text, Object...args) {

		String message = String.format(text, args);
		Shell shell = Display.getCurrent().getActiveShell();

		MessageDialog.openInformation(shell, title, message);
	}
}
