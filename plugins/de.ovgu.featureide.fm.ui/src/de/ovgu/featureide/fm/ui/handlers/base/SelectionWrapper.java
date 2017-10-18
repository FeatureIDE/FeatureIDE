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

import javax.annotation.CheckForNull;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;

/**
 * Iterates through an {@link ISelection} and casts the elements.
 *
 * @author Sebastian Krieter
 */
public class SelectionWrapper<T> {

	public static <R> R checkClass(Object element, Class<R> classType) {
		if (element.getClass() == classType) {
			return classType.cast(element);
		} else if (element instanceof IAdaptable) {
			// Cast is necessary, don't remove
			return (R) ((IAdaptable) element).getAdapter(classType);
		}
		return null;
	}

	public static <T> SelectionWrapper<T> init(IStructuredSelection selection, Class<T> type) {
		return new SelectionWrapper<T>(selection, type);
	}

	private final Class<T> type;
	private final Iterator<?> it;

	private SelectionWrapper(IStructuredSelection selection, Class<T> type) {
		this.type = type;
		this.it = selection.iterator();
	}

	@CheckForNull
	public T getNext() {
		while (it.hasNext()) {
			final T element = checkClass(it.next(), type);
			if (element != null) {
				return element;
			}
		}
		return null;
	}

}
