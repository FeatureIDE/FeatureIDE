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

import static de.ovgu.featureide.fm.core.localization.StringTable.INVALID_ATTRIBUTE_NAME_ERROR_MESSAGE;
import static de.ovgu.featureide.fm.core.localization.StringTable.INVALID_ATTRIBUTE_NAME_ERROR_TITLE;
import static de.ovgu.featureide.fm.core.localization.StringTable.INVALID_RECURSIVE_ATTRIBUTE_NAME_ERROR_MESSAGE;
import static de.ovgu.featureide.fm.core.localization.StringTable.INVALID_RECURSIVE_ATTRIBUTE_NAME_ERROR_TITLE;

import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.CellEditor;
import org.eclipse.jface.viewers.ColumnViewer;
import org.eclipse.jface.viewers.TextCellEditor;
import org.eclipse.swt.widgets.Composite;

import de.ovgu.featureide.fm.attributes.AttributeUtils;
import de.ovgu.featureide.fm.attributes.base.IExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;
import de.ovgu.featureide.fm.attributes.view.operations.ChangeAttributeNameOperation;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;

/**
 * Editing support for the name column of the {@link FeatureAttributeView}.
 *
 * @author Joshua Sprey
 * @author Chico Sundermann
 * @author Johannes Herschel
 */
public class FeatureAttributeNameEditingSupport extends AbstractFeatureAttributeEditingSupport {

	public FeatureAttributeNameEditingSupport(FeatureAttributeView view, ColumnViewer viewer, boolean enabled) {
		super(view, viewer, enabled);
	}

	@Override
	protected CellEditor getCellEditor(Object element) {
		return new TextCellEditor((Composite) getViewer().getControl());
	}

	@Override
	protected Object getValue(Object element) {
		final IFeatureAttribute attribute = (IFeatureAttribute) element;
		return attribute.getName();
	}

	@Override
	protected void setValue(Object element, Object value) {
		IFeatureAttribute attribute = (IFeatureAttribute) element;
		IExtendedFeature feature = (IExtendedFeature) attribute.getFeature();
		String newName = value.toString();

		// No further checks and no operation if no change occurred
		if (attribute.getName().equals(newName)) {
			return;
		}

		// Check for name conflicts
		if (feature.getAttribute(newName) != null) {
			MessageDialog.openError(null, INVALID_ATTRIBUTE_NAME_ERROR_TITLE, INVALID_ATTRIBUTE_NAME_ERROR_MESSAGE);
			return;
		}
		if (attribute.isRecursive()) {
			if (AttributeUtils.getChildAttribute(feature, newName) != null) {
				MessageDialog.openError(null, INVALID_RECURSIVE_ATTRIBUTE_NAME_ERROR_TITLE, INVALID_RECURSIVE_ATTRIBUTE_NAME_ERROR_MESSAGE);
				return;
			}
		}

		// Apply operation
		FeatureModelOperationWrapper.run(new ChangeAttributeNameOperation((IFeatureModelManager) view.getManager(), attribute, newName));
	}
}
