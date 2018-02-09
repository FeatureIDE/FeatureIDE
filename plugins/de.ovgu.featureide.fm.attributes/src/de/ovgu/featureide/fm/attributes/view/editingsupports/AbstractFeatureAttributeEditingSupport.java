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
package de.ovgu.featureide.fm.attributes.view.editingsupports;

import org.eclipse.jface.viewers.CellEditor;
import org.eclipse.jface.viewers.ColumnViewer;
import org.eclipse.jface.viewers.EditingSupport;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;

/**
 * TODO description
 *
 * @author Joshua
 */
public abstract class AbstractFeatureAttributeEditingSupport extends EditingSupport {

	public boolean enabled = false;
	protected FeatureAttributeView view;

	/**
	 * @param viewer
	 */
	public AbstractFeatureAttributeEditingSupport(FeatureAttributeView view, ColumnViewer viewer, boolean enabled) {
		super(viewer);
		this.view = view;
		this.enabled = enabled;
	}

	/**
	 * @param viewer
	 */
	public AbstractFeatureAttributeEditingSupport(ColumnViewer viewer) {
		super(viewer);
		enabled = false;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.EditingSupport#getCellEditor(java.lang.Object)
	 */
	@Override
	protected abstract CellEditor getCellEditor(Object element);

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.EditingSupport#canEdit(java.lang.Object)
	 */
	@Override
	protected boolean canEdit(Object element) {
		if (enabled) {
			if (element instanceof IFeatureAttribute) {
				IFeatureAttribute att = (IFeatureAttribute) element;
				if (att.isRecursive() && !att.isHeadOfRecursiveAttribute()) {
					return false;
				}
				return true;
			}
		}
		return false;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.EditingSupport#getValue(java.lang.Object)
	 */
	@Override
	protected abstract Object getValue(Object element);

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.EditingSupport#setValue(java.lang.Object, java.lang.Object)
	 */
	@Override
	protected abstract void setValue(Object element, Object value);

}
