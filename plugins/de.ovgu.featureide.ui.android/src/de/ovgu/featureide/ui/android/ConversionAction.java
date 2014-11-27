package de.ovgu.featureide.ui.android;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

import de.ovgu.featureide.ui.android.wizards.ConversionWizard;

/**
 * Starts the conversion wizard.
 * 
 * @author Lars-Christian Schulz
 * @author Eric Guimatsia
 */
public class ConversionAction implements IObjectActionDelegate {

	private ISelection selection;

	@Override
	public void run(IAction action) {
		if (selection instanceof IStructuredSelection) {
			ConversionWizard wizard = new ConversionWizard();
			wizard.init(null, (IStructuredSelection) selection);
			WizardDialog dialog = new WizardDialog(null, wizard);
			dialog.open();
		}
	}

	@Override
	public void selectionChanged(IAction action, ISelection selection) {
		this.selection = selection;
	}

	@Override
	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
	}

}
