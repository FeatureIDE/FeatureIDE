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
package de.ovgu.featureide.fm.ui.handlers.base;

import java.util.Arrays;
import java.util.Iterator;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.ITypeRoot;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.ui.javaeditor.EditorUtility;
import org.eclipse.jdt.internal.ui.javaeditor.JavaEditor;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.texteditor.ITextEditor;

/**
 * Abstract class for handlers that work on selections.
 * 
 * @author Sebastian Krieter
 */
public abstract class ASelectionHandler extends AbstractHandler {

	/**
	 * This method is called for every object in the current selection.
	 * 
	 * @param element the current object.
	 */
	protected abstract void singleAction(Object element);

	@Override
	public final Object execute(ExecutionEvent event) throws ExecutionException {
		final ISelection selection = HandlerUtil.getCurrentSelection(event);
		if (selection instanceof IStructuredSelection) {
			IStructuredSelection strSelection = (IStructuredSelection) selection;
			if (startAction(strSelection)) {
				for (Iterator<?> it = strSelection.iterator(); it.hasNext();) {
					singleAction(it.next());
				}
				endAction();
			}
		}
		else if (selection instanceof ITextSelection)
		{
			IWorkbenchPage page = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
			ITextEditor editor = (ITextEditor) page.getActiveEditor();
			IJavaElement elem = JavaUI.getEditorInputJavaElement(editor.getEditorInput());
			if (elem instanceof ICompilationUnit) {
			    ITextSelection sel = (ITextSelection) editor.getSelectionProvider().getSelection();
				
				ITypeRoot root = (ITypeRoot) JavaUI.getEditorInputJavaElement(editor.getEditorInput());
				IJavaElement[] elt;
				try {
//					 IJavaElement selected =  ((ICompilationUnit) elem).getElementAt(sel.getOffset());
//					 if (selected != null && selected.getElementType() == IJavaElement.METHOD) {
//						 singleAction((IMethod) selected);
//				    }
					elt = root.codeSelect(sel.getOffset(), sel.getLength());
					if (elt.length > 0) singleAction(elt[0]);
				} catch (JavaModelException e) {
					e.printStackTrace();
				}
			}
			
			
		}
		
		return null;
	}

	/**
	 * This method is called before iterating through the current selection.</br>
	 * Default implementation returns {@code true}.
	 * 
	 * @param selection the current selection
	 * 
	 * @return {@code true} if the handler should iterate through the current selection,</br> {@code false} if the handler should stop.
	 */
	protected boolean startAction(IStructuredSelection selection) {
		return true;
	}

	/**
	 * This method is called after the last object in the selection was handled.</br>
	 * Default implementation does nothing.
	 */
	protected void endAction() {
		// do nothing.
	}

}
