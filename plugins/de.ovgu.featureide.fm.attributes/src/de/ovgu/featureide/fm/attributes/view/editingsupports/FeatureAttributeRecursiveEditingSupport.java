/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
import org.eclipse.jface.viewers.CheckboxCellEditor;
import org.eclipse.jface.viewers.ColumnViewer;
import org.eclipse.swt.widgets.Composite;

import de.ovgu.featureide.fm.attributes.base.IExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;

/**
 * Editing support for the recursive column of the {@link FeatureAttributeView}. The boolean value of the column is shown as checkbox.
 *
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public class FeatureAttributeRecursiveEditingSupport extends AbstractFeatureAttributeEditingSupport {

	public FeatureAttributeRecursiveEditingSupport(FeatureAttributeView view, ColumnViewer viewer, boolean enabled) {
		super(view, viewer, enabled);
	}

	private static final String TRUE_STRING = "true";

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.attributes.editingsupport.AbstractFeatureAttributeEditingSupport#getCellEditor(java.lang.Object)
	 */
	@Override
	protected CellEditor getCellEditor(Object element) {
		return new CheckboxCellEditor((Composite) getViewer().getControl());
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.attributes.editingsupport.AbstractFeatureAttributeEditingSupport#getValue(java.lang.Object)
	 */
	@Override
	protected Object getValue(Object element) {
		final IFeatureAttribute attribute = (IFeatureAttribute) element;
		return attribute.isRecursive();
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.attributes.editingsupport.AbstractFeatureAttributeEditingSupport#setValue(java.lang.Object, java.lang.Object)
	 */
	@Override
	protected void setValue(Object element, Object value) {
		IFeatureAttribute attribute = (IFeatureAttribute) element;
		Boolean newRecursive = (Boolean) value;
		attribute.setRecursive(newRecursive);
		IFeature feat = attribute.getFeature();
		if (newRecursive) {
			if (!isNameUnique(attribute, feat)) {
				MessageDialog.openError(null, "Invalid recursive attribute name", "Please ensure the name is not used by an attribute of a child feature.");
				attribute.setRecursive(false);
				return;
			}
			attribute.recurseAttribute(feat);
		} else {
			attribute.deleteRecursiveAttributes(feat);
		}
		view.getManager().fireEvent(new FeatureIDEEvent(element, EventType.FEATURE_ATTRIBUTE_CHANGED, true, ((IFeatureAttribute) element).getFeature()));
	}

	private boolean isNameUnique(IFeatureAttribute attribute, IFeature feature) {
		for (IFeatureStructure struct : feature.getStructure().getChildren()) {
			IExtendedFeature feat = (IExtendedFeature) struct.getFeature();
			if (feat.isContainingAttribute(attribute)) {
				return false;
			}
			return isNameUnique(attribute, feat);
		}
		return true;
	}
}
