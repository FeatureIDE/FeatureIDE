package de.ovgu.featureide.fm.attributes.view;

import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;

public class FeatureAttributeViewSelectionFilter extends ViewerFilter {

	private FeatureAttributeView faView;

	FeatureAttributeViewSelectionFilter(FeatureAttributeView faView) {
		this.faView = faView;
	}

	@Override
	public boolean select(Viewer viewer, Object parentElement, Object element) {
		if (faView.selectedAutomaticFeatures == null || faView.selectedManualFeatures == null) {
			return true;
		} else {
			if (faView.selectedAutomaticFeatures.size() == 0 || faView.selectedManualFeatures.size() == 0) {
				return true;
			} else {
				if (viewer instanceof TreeViewer) {
					if (element instanceof IFeature && faView.selectedAutomaticFeatures.contains(element)) {
						return true;
					} else if (element instanceof IFeatureAttribute && faView.selectedManualFeatures.contains(parentElement)) {
						return true;
					} else {
						return false;
					}
				}
			}
		}
		return false;
	}

}
