/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.Iterator;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.handlers.HandlerUtil;

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
			final IStructuredSelection strSelection = (IStructuredSelection) selection;
			if (startAction(strSelection)) {
				for (final Iterator<?> it = strSelection.iterator(); it.hasNext();) {
					singleAction(it.next());
				}
				endAction();
			}
		}
		return null;
	}

	/**
	 * This method is called before iterating through the current selection.</br> Default implementation returns {@code true}.
	 *
	 * @param selection the current selection
	 *
	 * @return {@code true} if the handler should iterate through the current selection,</br> {@code false} if the handler should stop.
	 */
	protected boolean startAction(IStructuredSelection selection) {
		return true;
	}

	/**
	 * This method is called after the last object in the selection was handled.</br> Default implementation does nothing.
	 */
	protected void endAction() {
		// do nothing.
	}

}
