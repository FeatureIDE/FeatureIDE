package br.ufal.ic.colligens.controllers;

import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;

/**
 * @author thiago
 *
 */
public abstract class ViewController {

	private final String ID;
	private ViewPart view;

	/**
	 * @param ID
	 */
	public ViewController(String ID) {
		this.ID = ID;
	}

	public ViewPart getView() {
		return view;
	}

	public void setView(ViewPart view) {
		this.view = view;
	}

	/**
	 * open the view in workspace
	 */
	public void showView() {
		Display.getDefault().syncExec(new Runnable() {

			@Override
			public void run() {
				IWorkbenchWindow activeWindow;
				IWorkbenchPage activePage;
				activeWindow = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
				if (activeWindow != null) {
					activePage = activeWindow.getActivePage();
					if (activePage != null) {
						try {
							activePage.showView(ID);
						} catch (final PartInitException e) {
							e.printStackTrace();
						}
					}
				}
			}
		});
	}

}
