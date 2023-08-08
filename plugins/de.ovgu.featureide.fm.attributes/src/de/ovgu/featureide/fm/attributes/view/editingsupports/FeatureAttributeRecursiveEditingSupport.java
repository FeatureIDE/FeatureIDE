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

import static de.ovgu.featureide.fm.core.localization.StringTable.INVALID_RECURSIVE_ATTRIBUTE_NAME_ERROR_MESSAGE;
import static de.ovgu.featureide.fm.core.localization.StringTable.INVALID_RECURSIVE_ATTRIBUTE_NAME_ERROR_TITLE;

import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.CellEditor;
import org.eclipse.jface.viewers.ColumnViewer;
import org.eclipse.jface.viewers.ComboBoxViewerCellEditor;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;

import de.ovgu.featureide.fm.attributes.base.IExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;
import de.ovgu.featureide.fm.attributes.view.operations.ChangeAttributeRecursiveOperation;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;

/**
 * Editing support for the recursive column of the {@link FeatureAttributeView}. The boolean value of the column is shown as checkbox.
 *
 * @author Joshua Sprey
 * @author Chico Sundermann
 * @author Johannes Herschel
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
		Boolean[] items = { false, true };
		ComboBoxViewerCellEditor cellEditor = new ComboBoxViewerCellEditor((Composite) getViewer().getControl(), SWT.READ_ONLY);
		cellEditor.setLabelProvider(new LabelProvider());
		cellEditor.setContentProvider(ArrayContentProvider.getInstance());
		cellEditor.setInput(items);
		return cellEditor;
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
		final IFeatureAttribute attribute = (IFeatureAttribute) element;
		final IFeature feature = attribute.getFeature();
		final Boolean newRecursive = (Boolean) value;

		// Check for name conflicts
		if (newRecursive && !isNameUnique(attribute, feature)) {
			MessageDialog.openError(null, INVALID_RECURSIVE_ATTRIBUTE_NAME_ERROR_TITLE, INVALID_RECURSIVE_ATTRIBUTE_NAME_ERROR_MESSAGE);
			return;
		}

		// Apply operation
		FeatureModelOperationWrapper.run(new ChangeAttributeRecursiveOperation((IFeatureModelManager) view.getManager(), attribute, newRecursive));
	}

	private boolean isNameUnique(IFeatureAttribute attribute, IFeature feature) {
		for (IFeatureStructure struct : feature.getStructure().getChildren()) {
			final IExtendedFeature feat = (IExtendedFeature) struct.getFeature();
			if (feat.isContainingAttribute(attribute)) {
				return false;
			}
			return isNameUnique(attribute, feat);
		}
		return true;
	}
}
