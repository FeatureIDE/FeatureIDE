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
package de.ovgu.featureide.fm.attributes.view.operations;

import static de.ovgu.featureide.fm.core.localization.StringTable.CHANGE_CONFIGURABLE_ATTRIBUTE_VALUE_OPERATION_NAME;

import de.ovgu.featureide.fm.attributes.base.IExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.config.ExtendedConfiguration;
import de.ovgu.featureide.fm.attributes.config.ExtendedSelectableFeature;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AbstractConfigurationOperation;

/**
 * Operation to change the configured value of a configurable feature attribute. Enables undo/redo functionality.
 * 
 * @author Joshua Sprey
 * @author Chico Sundermann
 * @author Johannes Herschel
 */
public class ChangeConfigurableAttributeValueOperation<D> extends AbstractConfigurationOperation {

	/**
	 * The name of the feature containing the attribute to be modified.
	 */
	private final String featureName;
	/**
	 * The name of the attribute to be modified.
	 */
	private final String attributeName;
	/**
	 * The new configured value of the attribute after the operation. null if this operation resets the configured value to the default value of the attribute.
	 */
	private final D newValue;

	/**
	 * The old configured value of the attribute before the operation.
	 */
	private Object oldValue;
	/**
	 * True if this operation sets the initial configured value, false if the attribute had a configured value before the operation.
	 */
	private boolean firstOverwrite = true;

	public ChangeConfigurableAttributeValueOperation(ConfigurationManager configurationManager, IFeatureAttribute att, D newValue) {
		super(configurationManager, CHANGE_CONFIGURABLE_ATTRIBUTE_VALUE_OPERATION_NAME);
		featureName = att.getFeature().getName();
		attributeName = att.getName();
		this.newValue = newValue;
	}

	@Override
	protected FeatureIDEEvent operation(Configuration config) {
		final ExtendedConfiguration extConfig = (ExtendedConfiguration) config;
		final ExtendedSelectableFeature selectableFeat = extConfig.getSelectableFeature(featureName);
		final IFeatureAttribute att = ((IExtendedFeature) selectableFeat.getFeature()).getAttribute(attributeName);
		firstOverwrite = !selectableFeat.hasAttributeWithConfiguredValue(att);
		oldValue = selectableFeat.getAttributeValue(att);
		if (newValue != null) {
			selectableFeat.addConfigurableAttribute(attributeName, newValue.toString());
		} else {
			selectableFeat.removeConfigurableAttribute(att);
		}
		return new FeatureIDEEvent(selectableFeat, EventType.CONFIGURABLE_ATTRIBUTE_CHANGED, oldValue, newValue != null ? newValue.toString() : null);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(Configuration config) {
		final ExtendedConfiguration extConfig = (ExtendedConfiguration) config;
		final ExtendedSelectableFeature selectableFeat = extConfig.getSelectableFeature(featureName);
		final IFeatureAttribute att = ((IExtendedFeature) selectableFeat.getFeature()).getAttribute(attributeName);
		// Case: switch back to default value from model
		if (firstOverwrite) {
			selectableFeat.removeConfigurableAttribute(att);
		} else {
			selectableFeat.addConfigurableAttribute(attributeName, oldValue.toString());
		}
		return new FeatureIDEEvent(selectableFeat, EventType.CONFIGURABLE_ATTRIBUTE_CHANGED, newValue != null ? newValue.toString() : null, oldValue);
	}

	@Override
	protected int getChangeIndicator() {
		return ConfigurationManager.CHANGE_CONFIGURABLE_ATTRIBUTE;
	}
}
