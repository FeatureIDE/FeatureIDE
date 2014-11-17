/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.configuration;

import java.util.HashMap;

import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.ImageData;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * Provides labels and images for the configuration tree view.
 * 
 * @author Thomas Thuem
 */
public class AdvancedConfigurationLabelProvider extends ColumnLabelProvider implements GUIDefaults {

	private static HashMap<String, Image> combinedImages = new HashMap<String, Image>();

	@Override
	public String getText(Object o) {
		if (o instanceof SelectableFeature) {
			SelectableFeature feature = (SelectableFeature) o;
			return feature.getFeature().getDisplayName();
		}
		return o.toString();
	}
	
	@Override
	public Image getImage(Object o) {
		if (!(o instanceof SelectableFeature)) {
			return null;
		}
		final SelectableFeature selFeature = (SelectableFeature) o;
		final Feature feature = selFeature.getFeature();
		
		final Image image1 = getConnectionImage(feature);
		final Image image2 = getSelectionImage(selFeature);

		final ImageData imageData1 = image1.getImageData();
		final ImageData imageData2 = image2.getImageData();

		final String imageString = image1.toString() + image2.toString();

		final Image combinedImage = combinedImages.get(imageString);
		if (combinedImage == null) {
			final int distance = 5;
			final Image mergeImage = new Image(image1.getDevice(), imageData2.width * 2 + distance, imageData1.height);

			final GC gc = new GC(mergeImage);

			if (image1.equals(IMG_MANDATORY) || image1.equals(IMG_OPTIONAL)) {
				gc.drawImage(image1, 0, 0, imageData1.width, imageData1.height, 3, 3, imageData1.width, imageData1.height);
			} else {
				gc.drawImage(image1, 0, 0, imageData1.width, imageData1.height, 0, 0, imageData1.width, imageData1.height);
			}
			gc.drawImage(image2, 0, 0, imageData2.width, imageData2.height, imageData1.width + distance, 0, imageData2.width, imageData2.height);

			gc.dispose();

			if (feature.isRoot()) {
				image1.dispose();
			}

			combinedImages.put(imageString, mergeImage);
			return mergeImage;
		}
		return combinedImage;
	}

	private Image getConnectionImage(Feature feature) {
		if (!feature.isRoot()) {
			if (feature.getParent() != null) {
				if (feature.getParent().isOr()) {
					return IMG_OR;
				}
				if (feature.getParent().isAlternative()) {
					return IMG_XOR;
				}
			}
			if (feature.isMandatory()) {
				return IMG_MANDATORY;
			}
			return IMG_OPTIONAL;
		}
		return new Image(null, IMG_MANDATORY.getImageData().width, IMG_MANDATORY.getImageData().height);
	}

	private Image getSelectionImage(SelectableFeature feat) {
		if (feat.getAutomatic() != Selection.UNDEFINED) {
			return feat.getAutomatic() == Selection.SELECTED ? IMAGE_ASELECTED : IMAGE_ADESELECTED;
		}
		if (feat.getManual() == Selection.UNDEFINED) {
			return IMAGE_UNDEFINED;
		}
		return feat.getManual() == Selection.SELECTED ? IMAGE_SELECTED : IMAGE_DESELECTED;
	}

	@Override
	public void dispose() {
		super.dispose();
	}

	@Override
	public String getToolTipText(Object element) {
		if (element instanceof SelectableFeature) {
			SelectableFeature feature = (SelectableFeature) element;

			String relConst = feature.getFeature().getRelevantConstraintsString();
			String describ = feature.getFeature().getDescription();

			if (describ != null && !relConst.equals("")) {
				return "Description:\n" + describ + "\n\nConstraints:\n" + relConst;
			}
			if (describ != null && relConst.equals("")) {
				return "Description:\n" + describ;
			}
			if (describ == null && !relConst.equals("")) {
				return "Constraints:\n" + relConst;
			}
		}
		return null;
	}
}