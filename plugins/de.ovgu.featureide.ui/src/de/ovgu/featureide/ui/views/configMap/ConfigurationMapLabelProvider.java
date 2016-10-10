/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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

import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ITableColorProvider;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.core.base.IFeature;
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
	
	private ConfigurationMap configurationMap;

	public ConfigurationMapLabelProvider(ConfigurationMap configurationMap) {
		this.configurationMap = configurationMap;
	}

	@Override
	public boolean isLabelProperty(Object element, String property) {
		return false;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ITableColorProvider#getForeground(java.lang.Object, int)
	 */
	@Override
	public Color getForeground(Object element, int columnIndex) {
		return null;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ITableColorProvider#getBackground(java.lang.Object, int)
	 */
	@Override
	public Color getBackground(Object element, int columnIndex) {
		if (element instanceof IFeature) {
			IFeature feature = (IFeature) element;
			FeatureColor featureColor = FeatureColorManager.getColor(feature);
			return featureColor.toSwtColor();
		}
		return null;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ITableLabelProvider#getColumnImage(java.lang.Object, int)
	 */
	@Override
	public Image getColumnImage(Object element, int columnIndex) {
		if (element instanceof IFeature) {
			IFeature feature = (IFeature) element;
			int offset = configurationMap.getConfigurationColumnsOffset();

			if (columnIndex >= offset) {// && columnIndex < configurationMap.end) {
				Configuration config = configurationMap.getConfigurations().get(columnIndex - offset);

				String imgPath = imgUnselectedPath;
				if (config.getSelectedFeatures().contains(feature))
					imgPath = imgSelectedPath;

				return FMUIPlugin.getImage(imgPath);
			}
		}

		return null;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ITableLabelProvider#getColumnText(java.lang.Object, int)
	 */
	@Override
	public String getColumnText(Object element, int columnIndex) {		
		if (columnIndex < configurationMap.getConfigurationColumnsOffset()) {
			if (element instanceof IFeature)
				return element.toString();
		}
		
		return null;
	}

	@Override
	public void addListener(ILabelProviderListener listener) {
	}

	@Override
	public void removeListener(ILabelProviderListener listener) {
	}

	@Override
	public void dispose() {
	}
}
