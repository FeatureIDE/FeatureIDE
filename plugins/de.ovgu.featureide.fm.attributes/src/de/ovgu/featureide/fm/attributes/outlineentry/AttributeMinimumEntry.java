package de.ovgu.featureide.fm.attributes.outlineentry;

import java.util.List;

import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.DoubleFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.LongFeatureAttribute;
import de.ovgu.featureide.fm.attributes.computations.impl.EstimatedMinimumComputation;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry;

public class AttributeMinimumEntry implements IOutlineEntry {

	IFeatureAttribute attribute;
	Configuration config;
	EstimatedMinimumComputation estimatedMinimum;
	Double result;
	private String labelSuffix;

	private static final String EST = " (est)";
	private static final String LABEL = "Minimal sum of value: ";

	public AttributeMinimumEntry(Configuration config, IFeatureAttribute attribute) {
		this.config = config;
		this.attribute = attribute;
		estimatedMinimum = new EstimatedMinimumComputation(config, attribute);
		result = (Double) estimatedMinimum.getEstimatedMinimum();
		labelSuffix = EST;

	}

	@Override
	public String getLabel() {
		if (attribute instanceof LongFeatureAttribute) {
			return LABEL + String.valueOf(result.longValue()) + labelSuffix;
		}
		return LABEL + result.toString() + labelSuffix;
	}

	@Override
	public Image getLabelImage() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean hasChildren() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public List<IOutlineEntry> getChildren() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean supportsType(Object element) {
		return attribute instanceof LongFeatureAttribute || attribute instanceof DoubleFeatureAttribute;
	}

	@Override
	public void setConfig(Configuration config) {
		this.config = config;

	}

	@Override
	public void handleDoubleClick() {}

}
