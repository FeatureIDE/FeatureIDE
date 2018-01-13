package de.ovgu.featureide.fm.attributes.view.labelprovider;

import java.util.HashMap;

import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.jface.viewers.IColorProvider;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.color.ColorPalette;
import de.ovgu.featureide.fm.core.color.FeatureColor;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;

public abstract class FeatureAttributeColumnLabelProvider extends ColumnLabelProvider implements IColorProvider {

	protected HashMap<String, Image> cachedImages;
	private FeatureAttributeView view;

	public FeatureAttributeColumnLabelProvider(HashMap<String, Image> cachedImages, FeatureAttributeView view) {
		this.cachedImages = cachedImages;

		this.view = view;
	}

	@Override
	public Color getBackground(Object element) {
		if (element instanceof IFeatureAttribute) {
			IFeatureAttribute attribute = (IFeatureAttribute) element;
			IFeature feature = attribute.getFeature();
			if (view.selectedAutomaticFeatures == null || view.selectedManualFeatures == null) {
				final FeatureColor featureColor = FeatureColorManager.getColor(feature);
				return ColorPalette.toSwtColor(featureColor);
			} else {
				if (!view.selectedManualFeatures.contains(feature)) {
					return ColorPalette.toSwtColor(FeatureColor.Light_Gray);
				} else {
					return ColorPalette.toSwtColor(FeatureColor.Light_Green);
				}
			}
		}
		if (element instanceof IFeature) {
			IFeature feature = (IFeature) element;
			if (view.selectedAutomaticFeatures == null || view.selectedManualFeatures == null) {
				final FeatureColor featureColor = FeatureColorManager.getColor(feature);
				return ColorPalette.toSwtColor(featureColor);
			} else {
				if (!view.selectedManualFeatures.contains(feature)) {
					return ColorPalette.toSwtColor(FeatureColor.Light_Gray);
				} else {
					return ColorPalette.toSwtColor(FeatureColor.Light_Green);
				}
			}
		}
		return new Color(null, 255, 255, 255);
	}
}
