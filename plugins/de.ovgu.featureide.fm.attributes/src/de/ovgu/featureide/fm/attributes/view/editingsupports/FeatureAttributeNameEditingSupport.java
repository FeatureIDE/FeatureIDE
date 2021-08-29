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
import org.eclipse.jface.viewers.ColumnViewer;
import org.eclipse.jface.viewers.TextCellEditor;
import org.eclipse.swt.widgets.Composite;

import de.ovgu.featureide.fm.attributes.base.IExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;

/**
 * Editing support for the name column of the {@link FeatureAttributeView}.
 *
 * @author Joshua Sprey
 * @author Chico Sundermann
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
		IExtendedFeature feat = (IExtendedFeature) ((IFeatureAttribute) element).getFeature();
		for (IFeature f : feat.getFeatureModel().getFeatures()) {
			IExtendedFeature ext = (IExtendedFeature) f;
			for (IFeatureAttribute att : ext.getAttributes()) {
				if (att.getName().equals(value.toString()) && !((IFeatureAttribute) element).getType().equals(att.getType())) {
					MessageDialog.openError(null, "Invalid input", "The inserted attribute name is used on a different attribute type");
					return;
				}
			}
		}
		for (IFeatureAttribute att : feat.getAttributes()) {
			if (att.getName().equals(value.toString()) && att != (IFeatureAttribute) element) {
				MessageDialog.openError(null, "Invalid input", "Please insert a unique attribute name.");
				return;
			}
		}
		((IFeatureAttribute) element).setName(value.toString());
		if (((IFeatureAttribute) element).isRecursive()) {
			view.getManager().fireEvent(new FeatureIDEEvent(element, EventType.FEATURE_ATTRIBUTE_CHANGED, true, ((IFeatureAttribute) element).getFeature()));
		} else {
			view.getManager().fireEvent(new FeatureIDEEvent(element, EventType.FEATURE_ATTRIBUTE_CHANGED, false, ((IFeatureAttribute) element).getFeature()));
		}
		getViewer().update(element, null);
		view.repackAllColumns();
	}
}
