/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.views.configMap;

import java.util.HashMap;

import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ITableColorProvider;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.color.ColorPalette;
import de.ovgu.featureide.fm.core.color.FeatureColor;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * The Label Provider for the Configuration Map.
 *
 * @author Paul Maximilian Bittner
 */
public class ConfigurationMapLabelProvider implements ITableLabelProvider, ITableColorProvider {

	private final static String imgSelectedPath = "aselected.ico";
	private final static String imgUnselectedPath = "adeselected.ico";

	private final ConfigurationMap configurationMap;

	private final HashMap<String, Image> cachedImages;

	public ConfigurationMapLabelProvider(ConfigurationMap configurationMap) {
		this.configurationMap = configurationMap;

		cachedImages = new HashMap<String, Image>();
		FMUIPlugin.getDefault();
		cachedImages.put(imgSelectedPath, FMUIPlugin.getImage(imgSelectedPath));
		FMUIPlugin.getDefault();
		cachedImages.put(imgUnselectedPath, FMUIPlugin.getImage(imgUnselectedPath));
	}

	@Override
	public boolean isLabelProperty(Object element, String property) {
		return false;
	}

	@Override
	public Color getForeground(Object element, int columnIndex) {
		return null;
	}

	@Override
	public Color getBackground(Object element, int columnIndex) {
		if (columnIndex == configurationMap.getSelectedColumnIndex()) {
			return configurationMap.getColumnHighlightColor();
		} else if (element instanceof IFeature) {
			final IFeature feature = (IFeature) element;
			final FeatureColor featureColor = FeatureColorManager.getColor(feature);
			return ColorPalette.toSwtColor(featureColor);
		}
		return null;
	}

	@Override
	public Image getColumnImage(Object element, int columnIndex) {
		if (element instanceof IFeature) {
			final IFeature feature = (IFeature) element;
			if (configurationMap.isConfigColumn(columnIndex)) {// && columnIndex < configurationMap.end) {
				final Configuration config = configurationMap.getConfigurationOfColumn(columnIndex);

				if (!feature.getStructure().isAbstract()) {
					String imgPath = imgUnselectedPath;
					if (config.getSelectedFeatures().contains(feature)) {
						imgPath = imgSelectedPath;
					}

					return cachedImages.get(imgPath);
				}
			}
		}

		return null;
	}

	@Override
	public String getColumnText(Object element, int columnIndex) {
		if (configurationMap.getConfigColumnsOffset() > columnIndex) {
			if ((element instanceof IFeature) || (element instanceof String)) {
				return element.toString();
			}
		}

		return null;
	}

	@Override
	public void addListener(ILabelProviderListener listener) {}

	@Override
	public void removeListener(ILabelProviderListener listener) {}

	@Override
	public void dispose() {}

}
