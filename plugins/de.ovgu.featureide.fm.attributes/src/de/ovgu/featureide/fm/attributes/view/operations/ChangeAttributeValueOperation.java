package de.ovgu.featureide.fm.attributes.view.operations;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AbstractFeatureModelOperation;

public class ChangeAttributeValueOperation<D> extends AbstractFeatureModelOperation {

	private D value;

	private IFeatureAttribute att;

	private Object oldValue;

	public ChangeAttributeValueOperation(IFeatureModelManager fmManager, IFeatureAttribute att, D value) {
		super(fmManager, EventType.FEATURE_ATTRIBUTE_CHANGED.toString());
		this.att = att;
		this.value = value;
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel model) {
		oldValue = att.getValue();
		att.setValue(value);
		return new FeatureIDEEvent(att, EventType.FEATURE_ATTRIBUTE_CHANGED, false, att.getFeature());
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel model) {
		att.setValue(oldValue);
		return new FeatureIDEEvent(att, EventType.FEATURE_ATTRIBUTE_CHANGED, false, att.getFeature());
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_ATTRIBUTES;
	}

}
