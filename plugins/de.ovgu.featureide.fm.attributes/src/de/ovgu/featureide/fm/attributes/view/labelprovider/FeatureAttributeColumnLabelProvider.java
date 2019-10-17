/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 *
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.attributes.view.labelprovider;

import java.util.HashMap;

import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.jface.viewers.IColorProvider;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;
import de.ovgu.featureide.fm.core.AnalysesCollection;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.color.ColorPalette;
import de.ovgu.featureide.fm.core.color.FeatureColor;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;

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
			final FeatureModelFormula variableFormula = FeatureModelManager.getInstance(feature.getFeatureModel()).getVariableFormula();
			final AnalysesCollection properties = variableFormula.getAnalyzer().getAnalysesCollection();
			return feature.createTooltip(properties);
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
		// Display tooltip after 1000 ms (1sek)
		return 1000;
	}

	@Override
	public int getToolTipTimeDisplayed(Object object) {
		// Display tooltip for 15000 ms (15sek)
		return 15000;
	}
}
