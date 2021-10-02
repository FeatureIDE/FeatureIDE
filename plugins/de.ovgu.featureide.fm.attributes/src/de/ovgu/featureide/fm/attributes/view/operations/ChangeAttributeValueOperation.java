package de.ovgu.featureide.fm.attributes.view.operations;

import de.ovgu.featureide.fm.attributes.base.IExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AbstractFeatureModelOperation;

public class ChangeAttributeValueOperation<D> extends AbstractFeatureModelOperation {

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

	public ChangeAttributeValueOperation(IFeatureModelManager fmManager, IFeatureAttribute att, D value) {
		super(fmManager, "Edit Attribute Value");
		featureName = att.getFeature().getName();
		attributeName = att.getName();
		this.value = value;
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel model) {
		IFeature feature = model.getFeature(featureName);
		if (feature instanceof IExtendedFeature) {
			IExtendedFeature extendedFeature = (IExtendedFeature) feature;
			IFeatureAttribute attribute = extendedFeature.getAttribute(attributeName);
			if (attribute != null) {
				oldValue = attribute.getValue();
				attribute.setValue(value);
				return new FeatureIDEEvent(attribute, EventType.FEATURE_ATTRIBUTE_CHANGED, true, extendedFeature);
			}
		}
		return FeatureIDEEvent.getDefault(EventType.FEATURE_ATTRIBUTE_CHANGED);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel model) {
		IFeature feature = model.getFeature(featureName);
		if (feature instanceof IExtendedFeature) {
			IExtendedFeature extendedFeature = (IExtendedFeature) feature;
			IFeatureAttribute attribute = extendedFeature.getAttribute(attributeName);
			if (attribute != null) {
				attribute.setValue(oldValue);
				return new FeatureIDEEvent(attribute, EventType.FEATURE_ATTRIBUTE_CHANGED, true, extendedFeature);
			}
		}
		return FeatureIDEEvent.getDefault(EventType.FEATURE_ATTRIBUTE_CHANGED);
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_ATTRIBUTES;
	}
}
