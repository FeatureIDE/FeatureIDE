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

import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.CellEditor;
import org.eclipse.jface.viewers.ColumnViewer;
import org.eclipse.jface.viewers.TextCellEditor;
import org.eclipse.swt.widgets.Composite;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttribute;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;

/**
 * TODO description
 *
 * @author Joshua
 */
public class FeatureAttributeValueEditingSupport extends AbstractFeatureAttributeEditingSupport {

	/**
	 * @param viewer
	 * @param enabled
	 */
	public FeatureAttributeValueEditingSupport(FeatureAttributeView view, ColumnViewer viewer, boolean enabled) {
		super(view, viewer, enabled);
		// TODO Auto-generated constructor stub
	}

	private static final String TRUE_STRING = "true";

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.attributes.editingsupport.AbstractFeatureAttributeEditingSupport#getCellEditor(java.lang.Object)
	 */
	@Override
	protected CellEditor getCellEditor(Object element) {
		return new TextCellEditor((Composite) getViewer().getControl());
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.attributes.editingsupport.AbstractFeatureAttributeEditingSupport#getValue(java.lang.Object)
	 */
	@Override
	protected Object getValue(Object element) {
		final IFeatureAttribute attribute = (IFeatureAttribute) element;
		if (attribute.getValue() != null) {
			return attribute.getValue().toString();
		}
		return "";
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.attributes.editingsupport.AbstractFeatureAttributeEditingSupport#setValue(java.lang.Object, java.lang.Object)
	 */
	@Override
	protected void setValue(Object element, Object value) {
		final IFeatureAttribute attribute = (IFeatureAttribute) element;
		if (value == null || value.toString().equals("")) {
			((IFeatureAttribute) element).setValue(null);
			getViewer().update(element, null);
			return;
		}
		if (attribute.getType().equals(FeatureAttribute.BOOLEAN)) {
			if (value.toString().toLowerCase().equals(TRUE_STRING)) {
				((IFeatureAttribute) element).setValue(new Boolean(true));
				view.getFeatureModel().fireEvent(new FeatureIDEEvent(element, EventType.FEATURE_ATTRIBUTE_CHANGED));
			} else {
				((IFeatureAttribute) element).setValue(new Boolean(false));
				view.getFeatureModel().fireEvent(new FeatureIDEEvent(element, EventType.FEATURE_ATTRIBUTE_CHANGED));
			}
		} else if (attribute.getType().equals(FeatureAttribute.STRING)) {
			((IFeatureAttribute) element).setValue(value.toString());
			view.getFeatureModel().fireEvent(new FeatureIDEEvent(element, EventType.FEATURE_ATTRIBUTE_CHANGED));
		} else if (attribute.getType().equals(FeatureAttribute.LONG)) {
			try {
				final long temp = Long.parseLong(value.toString());
				((IFeatureAttribute) element).setValue(new Long(temp));
				view.getFeatureModel().fireEvent(new FeatureIDEEvent(element, EventType.FEATURE_ATTRIBUTE_CHANGED));
			} catch (final NumberFormatException e) {
				MessageDialog.openError(null, "Invalid input", "Please insert a valid integer number.");
			}
		} else if (attribute.getType().equals(FeatureAttribute.DOUBLE)) {
			try {
				final double temp = Double.parseDouble(value.toString());
				((IFeatureAttribute) element).setValue(new Double(temp));
				view.getFeatureModel().fireEvent(new FeatureIDEEvent(element, EventType.FEATURE_ATTRIBUTE_CHANGED));
			} catch (final NumberFormatException e) {
				MessageDialog.openError(null, "Invalid input", "Please insert a valid float number.");
			}
		}
		getViewer().update(element, null);
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.EditingSupport#canEdit(java.lang.Object)
	 */
	@Override
	protected boolean canEdit(Object element) {
		return enabled && (element instanceof IFeatureAttribute);
	}
}
