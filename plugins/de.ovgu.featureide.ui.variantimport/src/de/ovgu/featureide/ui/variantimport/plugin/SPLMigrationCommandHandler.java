/**
 * 
 */
package de.ovgu.featureide.ui.variantimport.plugin;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.handlers.HandlerUtil;

import de.ovgu.featureide.ui.variantimport.migration.VariantsToFeatureHouseSPLMigrator;
import de.ovgu.featureide.ui.variantimport.wizard.SPLMigrationWizard;

/**
 * This class handles the {@code SPLMigrationCommand} which is triggered by the
 * context menu on a selection of projects in the eclipse packet manager.
 * Most of the Implementation is handled by the {@link SPLMigrationWizard}.
 * 
 * @author Konstantin Tonscheidt
 * 
 */
public class SPLMigrationCommandHandler extends AbstractHandler
{

	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException
	{
		IStructuredSelection currentSelection = null;
		if (HandlerUtil.getCurrentSelection(event) instanceof IStructuredSelection)
			currentSelection = (IStructuredSelection) HandlerUtil
					.getCurrentSelection(event);

		new VariantsToFeatureHouseSPLMigrator(currentSelection);
		
		return null;
	}

}
