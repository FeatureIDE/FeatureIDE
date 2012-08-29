/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.ui.views.collaboration.color.action;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.graphics.ImageData;
import org.eclipse.swt.graphics.PaletteData;
import org.eclipse.swt.graphics.RGB;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.ui.color.ColorPalette;
import de.ovgu.featureide.ui.views.collaboration.CollaborationView;

/**
 * TODO description
 * 
 * @author Sebastian Krieter
 */
public class SetColorAction extends AbstractColorAction {

	private final class ColorDescriptor extends ImageDescriptor {
		private final ImageData id;

		public ColorDescriptor(int color, float transparency) {
			id = new ImageData(20, 20, 1, 
					new PaletteData(new RGB[]{ColorPalette.getRGB(color, transparency)}));
		}

		@Override
		public ImageData getImageData() {
			return id;
		}
	}

	public SetColorAction(GraphicalViewerImpl view,
			CollaborationView collaborationView, int index) {
		super(ColorPalette.getColorName(index), view, collaborationView, index);
		setImageDescriptor(new ColorDescriptor(index, 0.2f));
	}
	
	@Override
	protected boolean action(FeatureModel fm, String collName) {
		Feature feat = fm.getFeature(collName);
		if (feat != null && feat.getColor() != index) {
			feat.setColor(index);
			return true;
		}
		return false;
	}
}