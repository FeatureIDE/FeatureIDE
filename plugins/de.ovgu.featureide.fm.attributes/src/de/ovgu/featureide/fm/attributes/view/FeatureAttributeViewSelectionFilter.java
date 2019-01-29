package de.ovgu.featureide.fm.attributes.view;

import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;

/**
 * Realizes filtering for the {@link FeatureAttributeView}. Only selected features of the {@link FeatureDiagramEditor} are shown when the filter is activated.
 * 
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public class FeatureAttributeViewSelectionFilter extends ViewerFilter {

	private FeatureAttributeView faView;

	FeatureAttributeViewSelectionFilter(FeatureAttributeView faView) {
		this.faView = faView;
	}

	@Override
	public boolean select(Viewer viewer, Object parentElement, Object element) {
		if (faView.selectedAutomaticFeatures == null || faView.selectedManualFeatures == null) {
			if (faView.getFeatureModel() != null) {
				return element == FeatureAttributeContentProvider.PLEASE_SELECT_A_FEATURE_IN_THE_FEATURE_DIAGRAM ? true : false;
			} else {
				return true;
			}
		} else {
			if (faView.selectedAutomaticFeatures.size() == 0 || faView.selectedManualFeatures.size() == 0) {
				if (faView.getFeatureModel() != null) {
					return element == FeatureAttributeContentProvider.PLEASE_SELECT_A_FEATURE_IN_THE_FEATURE_DIAGRAM ? true : false;
				} else {
					return true;
				}
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
