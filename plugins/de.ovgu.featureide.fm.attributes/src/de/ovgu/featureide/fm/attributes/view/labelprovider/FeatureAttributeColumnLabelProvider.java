package de.ovgu.featureide.fm.attributes.view.labelprovider;

import java.util.HashMap;

import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.jface.viewers.IColorProvider;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.color.ColorPalette;
import de.ovgu.featureide.fm.core.color.FeatureColor;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;

/**
 * Abstract label provider that is subclassed by every label provider of the {@link FeatureAttributeView}.
 * 
 * @author Joshuas Sprey
 * @author Chico Sundermann
 */
public abstract class FeatureAttributeColumnLabelProvider extends ColumnLabelProvider implements IColorProvider {

	protected HashMap<String, Image> cachedImages;
	protected FeatureAttributeView view;

	public FeatureAttributeColumnLabelProvider(HashMap<String, Image> cachedImages, FeatureAttributeView view) {
		this.cachedImages = cachedImages;

		this.view = view;
	}

	@Override
	public Color getBackground(Object element) {
		if (element instanceof IFeatureAttribute) {
			IFeatureAttribute attribute = (IFeatureAttribute) element;
			IFeature feature = attribute.getFeature();
			final FeatureColor featureColor = FeatureColorManager.getColor(feature);
			return ColorPalette.toSwtColor(featureColor);
		}
		if (element instanceof IFeature) {
			IFeature feature = (IFeature) element;
			final FeatureColor featureColor = FeatureColorManager.getColor(feature);
			return ColorPalette.toSwtColor(featureColor);
		}
		return null;
	}

	@Override
	public String getToolTipText(Object element) {
		if (element instanceof IFeature) {
			IFeature feature = (IFeature) element;
			return feature.createTooltip(new Object[0]);
		} else {
			return null;
		}
	}

	@Override
	public Point getToolTipShift(Object object) {
		return new Point(5, 5);
	}

	@Override
	public int getToolTipDisplayDelayTime(Object object) {
		// Dsiplay tooltip after 1000 ms (1sek)
		return 1000;
	}

	@Override
	public int getToolTipTimeDisplayed(Object object) {
		// Dsiplay tooltip for 15000 ms (15sek)
		return 15000;
	}
}
