/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.refactoring.actions;

import java.util.Iterator;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.editors.text.TextEditor;

import de.ovgu.featureide.refactoring.windows.ExtractMethodWindow;

/**
 * A Jak refactoring to extract a method.
 * 
 * @author Stephan Kauschka
 */
public class ExtractMethodAction implements IObjectActionDelegate {

    private ISelection selection;
    private IWorkbenchPart workbenchPart;

    public ExtractMethodAction() {
	super();
    }

    public void setActivePart(IAction action, IWorkbenchPart targetPart) {
	this.workbenchPart = targetPart;
    }

    public void run(IAction action) {

	if (this.selection instanceof IStructuredSelection){
	    for (Iterator<?> iter = ((IStructuredSelection) this.selection).iterator(); iter.hasNext();) {
		Object element = iter.next();
		IFile file = null;

		if (element instanceof IFile)
		    file = (IFile) element;
		else if (element instanceof IAdaptable)
		    file = (IFile) ((IAdaptable) element).getAdapter(IFile.class);

		if (file != null){

		    //if workbenchPart is instance of TextEditor determine the click-target
		    if(this.workbenchPart instanceof TextEditor){
			ITextSelection sel = (ITextSelection) ((TextEditor) this.workbenchPart).getSelectionProvider().getSelection();
			new ExtractMethodWindow(file,sel);
		    }
		    //else the modifier to be changed is a classmodifier
		    else{
			new ExtractMethodWindow(file,null);
		    }
		}
	    }
	}
    }

    public void selectionChanged(IAction action, ISelection selection) {
	this.selection = selection;
    }
}
