package de.ovgu.featureide.cloneanalysis.views;

import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;

import de.ovgu.featureide.cloneanalysis.impl.CloneOccurence;
import de.ovgu.featureide.cloneanalysis.results.FeatureRootLocation;
import de.ovgu.featureide.cloneanalysis.results.VariantAwareClone;

final class FeatureFilter extends ViewerFilter {
	private FeatureRootLocation feature;

	public FeatureFilter(FeatureRootLocation featureRoot) {
		this.feature = featureRoot;
		System.out.println("created filter with feature " + getFeature().getLocation().toString());
	}

	@Override
	public boolean select(Viewer viewer, Object parentElement, Object element) {
		VariantAwareClone clone = null;
		CloneAnalysisView.totalEntries++;

		if (parentElement instanceof VariantAwareClone)
			clone = (VariantAwareClone) parentElement;

		if (parentElement != null) {
			String foo = (parentElement instanceof VariantAwareClone) ? "instance of VAClone"
					: "not instance of VAClone ";
			System.out.println("parentElement is " + foo);
		}

		if (containsFeature(clone))
			return true;

		if (element instanceof VariantAwareClone)
			clone = (VariantAwareClone) element;

		if (element != null) {
			String foo = (element instanceof VariantAwareClone) ? "instance of VAClone" : "not instance of VAClone ";
			System.out.println("element is " + foo);
		}

		if (containsFeature(clone))
			return true;

		CloneAnalysisView.hiddenEntries++;
		System.out.println(
				"neither " + parentElement + " nor " + element + " are part of feature " + getFeature().getLocation());
		return false;
	}

	private boolean containsFeature(VariantAwareClone clone) {
		if (clone == null)
			return false;

		for (CloneOccurence occurrence : clone.getOccurences()) {
			if (getFeature().getLocation().isPrefixOf(occurrence.getFile()))
				return true;
		}

		return false;
	}

	/**
	 * @return the feature
	 */
	public FeatureRootLocation getFeature() {
		return feature;
	}
}