/**
 * 
 */
package de.ovgu.featureide.core.variantimport;

import java.util.Iterator;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.ui.handlers.HandlerUtil;

/**
 * Implements the behavior of the {@linkplain VariantImportCommand}
 * 
 * @author Konstantin Tonscheidt
 *
 */
public class VariantImportCommandHandler extends AbstractHandler
{

	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException
	{
		// TODO do useful stuff
		
		if(HandlerUtil.getCurrentSelection(event) instanceof StructuredSelection)
		{
			StructuredSelection currentSelection = (StructuredSelection) HandlerUtil.getCurrentSelection(event);
			Iterator<?> iterator = currentSelection.iterator();
			while(iterator.hasNext())
			{
				Object selectedObject = iterator.next();
				IProject project = null;

				if(selectedObject instanceof IProject)
					project = (IProject) selectedObject;
				else if(selectedObject instanceof IAdaptable)
					project = (IProject) ((IAdaptable)selectedObject).getAdapter(IProject.class);
		
				doStuff(project);
			}
		}
		return null;
	}

	private void doStuff(IProject project)
	{
		if(project == null)
			return;
		// TODO doActualStuff
		
	}
	
}
