/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
/**
 * 
 */
package featureide.fm.ui.editors.configuration;

import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;

import featureide.fm.core.configuration.Configuration;
import featureide.fm.core.configuration.SelectableFeature;
import featureide.fm.core.configuration.Selection;
import featureide.fm.ui.FMUIPlugin;

/**
 * Provides labels and images for the configuration tree view.
 * 
 * @author Thomas Thuem
 */
public class ConfigurationLabelProvider extends LabelProvider {

	public final Image IMAGE_UNDEFINED, IMAGE_SELECTED, IMAGE_DESELECTED,
	IMAGE_ASELECTED, IMAGE_ADESELECTED;

	public ConfigurationLabelProvider() {
		IMAGE_UNDEFINED = FMUIPlugin.getImage("undefined.ico");
		IMAGE_SELECTED = FMUIPlugin.getImage("selected.ico");
		IMAGE_DESELECTED = FMUIPlugin.getImage("deselected.ico");
		IMAGE_ASELECTED = FMUIPlugin.getImage("aselected.ico");
		IMAGE_ADESELECTED = FMUIPlugin.getImage("adeselected.ico");
	}
	
	public String getText(Object o) {
		if (o instanceof SelectableFeature) {
			SelectableFeature feature = (SelectableFeature) o;
			if (feature.getParent() == null) {
				Configuration configuration = feature.getConfiguration();
				String s = configuration.valid() ? "valid" : "invalid";
				s += ", ";
				long number = configuration.number();
				if (number < 0)
					s += "more than " + (-1 - number) + " solutions";
				else
					s += number + " solutions";
				return feature.getName() + " (" + s + ")";
			}
			return feature.getName();
		}
		return o.toString();
	}

	public Image getImage(Object o) {
		if (!(o instanceof SelectableFeature))
			return null;
		SelectableFeature feature = (SelectableFeature) o;
		if (feature.getAutomatic() != Selection.UNDEFINED)
			return feature.getAutomatic() == Selection.SELECTED ? IMAGE_ASELECTED
					: IMAGE_ADESELECTED;
		if (feature.getManual() == Selection.UNDEFINED)
			return IMAGE_UNDEFINED;
		return feature.getManual() == Selection.SELECTED ? IMAGE_SELECTED
				: IMAGE_DESELECTED;
	}

	@Override
	public void dispose() {
		IMAGE_UNDEFINED.dispose();
		IMAGE_SELECTED.dispose();
		IMAGE_DESELECTED.dispose();
		IMAGE_ASELECTED.dispose();
		IMAGE_ADESELECTED.dispose();
		super.dispose();
	}

}
