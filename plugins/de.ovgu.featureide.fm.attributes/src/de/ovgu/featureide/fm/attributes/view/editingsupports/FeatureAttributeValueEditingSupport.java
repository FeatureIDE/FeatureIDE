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

import java.util.Objects;

import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.CellEditor;
import org.eclipse.jface.viewers.ColumnViewer;
import org.eclipse.jface.viewers.ComboBoxViewerCellEditor;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.TextCellEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttribute;
import de.ovgu.featureide.fm.attributes.config.ExtendedSelectableFeature;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView.FeatureAttributeOperationMode;
import de.ovgu.featureide.fm.attributes.view.operations.ChangeAttributeValueOperation;
import de.ovgu.featureide.fm.attributes.view.operations.ChangeConfigurableAttributeValueOperation;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.configuration.ConfigurationEditor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;

/**
 * Editing support for the value column of the {@link FeatureAttributeView}.
 *
 * @author Joshua Sprey
 * @author Chico Sundermann
 * @author Johannes Herschel
 */
public class FeatureAttributeValueEditingSupport extends AbstractFeatureAttributeEditingSupport {

	public FeatureAttributeValueEditingSupport(FeatureAttributeView view, ColumnViewer viewer, boolean enabled) {
		super(view, viewer, enabled);
	}

	private static final String TRUE_STRING = "true";

	@Override
	protected CellEditor getCellEditor(Object element) {
		final IFeatureAttribute attribute = (IFeatureAttribute) element;
		if (attribute.getType().equals(FeatureAttribute.BOOLEAN)) {
			String[] items = { "", "false", "true" };
			ComboBoxViewerCellEditor cellEditor = new ComboBoxViewerCellEditor((Composite) getViewer().getControl(), SWT.READ_ONLY);
			cellEditor.setLabelProvider(new LabelProvider());
			cellEditor.setContentProvider(ArrayContentProvider.getInstance());
			cellEditor.setInput(items);
			return cellEditor;
		} else {
			return new TextCellEditor((Composite) getViewer().getControl());
		}
	}

	@Override
	protected Object getValue(Object element) {
		final IFeatureAttribute attribute = (IFeatureAttribute) element;
		if (view.getCurrentEditor() instanceof ConfigurationEditor) {
			Configuration config = ((ConfigurationEditor) view.getCurrentEditor()).getConfigurationManager().getVarObject();
			for (SelectableFeature feat : config.getFeatures()) {
				if (feat.getFeature().getName().equals(attribute.getFeature().getName())) {
					if (feat instanceof ExtendedSelectableFeature) {
						ExtendedSelectableFeature extSelectable = (ExtendedSelectableFeature) feat;
						Object value = extSelectable.getAttributeValue(attribute);
						if (value != null) {
							return value.toString();
						} else {
							return "";
						}
					}
				}
			}
		}
		if (attribute.getValue() != null) {
			return attribute.getValue().toString();
		}
		return "";
	}

	@Override
	protected void setValue(Object element, Object value) {
		final IFeatureAttribute attribute = (IFeatureAttribute) element;
		final String valueString = value == null || value.toString().equals("") ? null : value.toString();
		if (view.getMode() == FeatureAttributeOperationMode.CONFIGURATION_EDITOR) {
			setValueInConfig(attribute, valueString);
			getViewer().update(element, null);
			view.repackAllColumns();
		} else if (view.getMode() == FeatureAttributeOperationMode.FEATURE_DIAGRAM) {
			setValueInFeatureDiagram(attribute, valueString);
			// Visual update handled by attribute view event handler in this case
		}
	}

	/**
	 * Sets the configured value of the given attribute using an operation.
	 * 
	 * @param attribute The configurable attribute
	 * @param value The new configured attribute value
	 */
	private void setValueInConfig(IFeatureAttribute attribute, String value) {
		if (value == null || attribute.isValidValue(value)) {
			final ConfigurationManager manager = (ConfigurationManager) view.getManager();
			switch (attribute.getType()) {
			case FeatureAttribute.BOOLEAN: {
				final Boolean v = value == null ? null : value.toLowerCase().equals(TRUE_STRING);
				final ChangeConfigurableAttributeValueOperation<Boolean> op = new ChangeConfigurableAttributeValueOperation<Boolean>(manager, attribute, v);
				op.execute();
				break;
			}
			case FeatureAttribute.DOUBLE: {
				final Double v = value == null ? null : Double.parseDouble(value);
				final ChangeConfigurableAttributeValueOperation<Double> op = new ChangeConfigurableAttributeValueOperation<Double>(manager, attribute, v);
				op.execute();
				break;
			}
			case FeatureAttribute.LONG: {
				final Long v = value == null ? null : Long.parseLong(value);
				final ChangeConfigurableAttributeValueOperation<Long> op = new ChangeConfigurableAttributeValueOperation<Long>(manager, attribute, v);
				op.execute();
				break;
			}
			case FeatureAttribute.STRING: {
				final ChangeConfigurableAttributeValueOperation<String> op = new ChangeConfigurableAttributeValueOperation<String>(manager, attribute, value);
				op.execute();
				break;
			}
			}
		}
	}

	/**
	 * Sets the value of the given attribute using an operation.
	 * 
	 * @param attribute The attribute to be edited
	 * @param value The new attribute value
	 */
	private void setValueInFeatureDiagram(IFeatureAttribute attribute, String value) {
		if (value == null || attribute.isValidValue(value)) {
			final IFeatureModelManager manager = (IFeatureModelManager) view.getManager();
			switch (attribute.getType()) {
			case FeatureAttribute.BOOLEAN: {
				final Boolean v = value == null ? null : value.toLowerCase().equals(TRUE_STRING);
				if (!Objects.equals(attribute.getValue(), v)) {
					FeatureModelOperationWrapper.run(new ChangeAttributeValueOperation<Boolean>(manager, attribute, v));
				}
				break;
			}
			case FeatureAttribute.DOUBLE: {
				final Double v = value == null ? null : Double.parseDouble(value);
				if (!Objects.equals(attribute.getValue(), v)) {
					FeatureModelOperationWrapper.run(new ChangeAttributeValueOperation<Double>(manager, attribute, v));
				}
				break;
			}
			case FeatureAttribute.LONG: {
				final Long v = value == null ? null : Long.parseLong(value);
				if (!Objects.equals(attribute.getValue(), v)) {
					FeatureModelOperationWrapper.run(new ChangeAttributeValueOperation<Long>(manager, attribute, v));
				}
				break;
			}
			case FeatureAttribute.STRING: {
				if (!Objects.equals(attribute.getValue(), value)) {
					FeatureModelOperationWrapper.run(new ChangeAttributeValueOperation<String>(manager, attribute, value));
				}
				break;
			}
			}
		}
	}

	@Override
	protected boolean canEdit(Object element) {
		return enabled && (element instanceof IFeatureAttribute);
	}
}
