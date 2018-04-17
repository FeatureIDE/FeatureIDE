package de.ovgu.featureide.oscar.propertyusage.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.wizard.IWizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.handlers.HandlerUtil;

import de.ovgu.featureide.oscar.propertyusage.wizard.PropertyUsageWizard;



/**
 * Our PropertyUsageHandler handler extends AbstractHandler, an IHandler base class.
 * 
 * @see org.eclipse.core.commands.IHandler
 * @see org.eclipse.core.commands.AbstractHandler
 */
public class PropertyUsageHandler extends AbstractHandler {
	
	protected IWizard wizard;


	@Override
	public final Object execute(ExecutionEvent event) throws ExecutionException {
	
		Shell activeShell = HandlerUtil.getActiveShell(event);

		IWizard wizard = new PropertyUsageWizard();

		WizardDialog dialog = new WizardDialog(activeShell, wizard);

		dialog.open();

		return null;
	}

	






}
