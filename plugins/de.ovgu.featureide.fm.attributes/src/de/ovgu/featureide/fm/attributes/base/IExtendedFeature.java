package de.ovgu.featureide.fm.attributes.base;

import java.util.List;

import de.ovgu.featureide.fm.core.base.IFeature;

public interface IExtendedFeature extends IFeature {

	public List<IFeatureAttribute> getAttributes();

	public void addAttribute(IFeatureAttribute attribute);

	public void removeAttribute(IFeatureAttribute attribute);

	public boolean isContainingAttribute(IFeatureAttribute attribute);

}
