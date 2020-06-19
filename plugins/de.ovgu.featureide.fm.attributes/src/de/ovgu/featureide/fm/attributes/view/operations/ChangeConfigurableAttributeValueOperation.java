package de.ovgu.featureide.fm.attributes.view.operations;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.config.ExtendedConfiguration;
import de.ovgu.featureide.fm.attributes.config.ExtendedSelectableFeature;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AbstractConfigurationOperation;

public class ChangeConfigurableAttributeValueOperation<D> extends AbstractConfigurationOperation {

	private D value;

	private IFeatureAttribute att;

	private Object oldValue;

	private boolean firstOverwrite = true;

	public ChangeConfigurableAttributeValueOperation(ConfigurationManager configurationManager, IFeatureAttribute att, D value) {
		super(configurationManager, EventType.CONFIGURABLE_ATTRIBUTE_CHANGED.toString());
		this.att = att;
		this.value = value;
	}

	@Override
	protected FeatureIDEEvent operation(Configuration config) {
		ExtendedConfiguration extConfig = (ExtendedConfiguration) config;
		ExtendedSelectableFeature selectableFeat = extConfig.getSelectableFeature(att.getFeature());
		firstOverwrite = selectableFeat.hasAttributeWithConfiguredValue(att);
		oldValue = selectableFeat.getAttributeValue(att);
		selectableFeat.addConfigurableAttribute(att.getName(), value.toString());
		return new FeatureIDEEvent(selectableFeat, EventType.CONFIGURABLE_ATTRIBUTE_CHANGED, oldValue, value.toString());
	}

	@Override
	protected FeatureIDEEvent inverseOperation(Configuration config) {
		ExtendedConfiguration extConfig = (ExtendedConfiguration) config;
		ExtendedSelectableFeature selectableFeat = extConfig.getSelectableFeature(att.getFeature());
		oldValue = selectableFeat.getAttributeValue(att);
		// Case: switch back to default value from model
		if (firstOverwrite) {
			selectableFeat.removeConfigurableAttribute(att);
		} else {
			selectableFeat.addConfigurableAttribute(att.getName(), oldValue.toString());
		}
		return new FeatureIDEEvent(selectableFeat, EventType.CONFIGURABLE_ATTRIBUTE_CHANGED, value.toString(), oldValue);
	}

	@Override
	protected int getChangeIndicator() {
		return ConfigurationManager.CHANGE_CONFIGURABLE_ATTRIBUTE;
	}

}
