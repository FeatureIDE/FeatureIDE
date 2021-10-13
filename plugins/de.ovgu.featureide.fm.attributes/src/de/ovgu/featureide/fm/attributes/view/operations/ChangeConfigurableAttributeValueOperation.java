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

public class ChangeConfigurableAttributeValueOperation<D> extends AbstractConfigurationOperation {

	/**
	 * The name of the feature containing the attribute to be modified.
	 */
	private final String featureName;
	/**
	 * The name of the attribute to be modified.
	 */
	private final String attributeName;

	private D value;

	private Object oldValue;

	private boolean firstOverwrite = true;

	public ChangeConfigurableAttributeValueOperation(ConfigurationManager configurationManager, IFeatureAttribute att, D value) {
		super(configurationManager, CHANGE_CONFIGURABLE_ATTRIBUTE_VALUE_OPERATION_NAME);
		featureName = att.getFeature().getName();
		attributeName = att.getName();
		this.value = value;
	}

	@Override
	protected FeatureIDEEvent operation(Configuration config) {
		ExtendedConfiguration extConfig = (ExtendedConfiguration) config;
		ExtendedSelectableFeature selectableFeat = extConfig.getSelectableFeature(featureName);
		IFeatureAttribute att = ((IExtendedFeature) selectableFeat.getFeature()).getAttribute(attributeName);
		firstOverwrite = selectableFeat.hasAttributeWithConfiguredValue(att);
		oldValue = selectableFeat.getAttributeValue(att);
		if (value != null) {
			selectableFeat.addConfigurableAttribute(attributeName, value.toString());
		} else {
			selectableFeat.removeConfigurableAttribute(att);
		}
		return new FeatureIDEEvent(selectableFeat, EventType.CONFIGURABLE_ATTRIBUTE_CHANGED, oldValue, value != null ? value.toString() : null);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(Configuration config) {
		ExtendedConfiguration extConfig = (ExtendedConfiguration) config;
		ExtendedSelectableFeature selectableFeat = extConfig.getSelectableFeature(featureName);
		IFeatureAttribute att = ((IExtendedFeature) selectableFeat.getFeature()).getAttribute(attributeName);
		// Case: switch back to default value from model
		if (firstOverwrite) {
			selectableFeat.removeConfigurableAttribute(att);
		} else {
			selectableFeat.addConfigurableAttribute(attributeName, oldValue.toString());
		}
		return new FeatureIDEEvent(selectableFeat, EventType.CONFIGURABLE_ATTRIBUTE_CHANGED, value != null ? value.toString() : null, oldValue);
	}

	@Override
	protected int getChangeIndicator() {
		return ConfigurationManager.CHANGE_CONFIGURABLE_ATTRIBUTE;
	}
}
