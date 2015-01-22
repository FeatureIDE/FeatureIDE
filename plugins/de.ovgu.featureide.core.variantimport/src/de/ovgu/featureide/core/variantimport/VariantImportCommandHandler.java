/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
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
