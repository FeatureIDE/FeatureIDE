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
package de.ovgu.featureide.ui.views.collaboration.action;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.graphics.ImageData;
import org.eclipse.swt.graphics.PaletteData;
import org.eclipse.swt.graphics.RGB;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.ui.editors.annotation.ColorPalette;
import de.ovgu.featureide.ui.views.collaboration.CollaborationView;

/**
 * Action to assign a color to a feature and remove it
 * 
 * @author Sebastian Krieter
 */
public class SetColorAction extends AbstractColorAction {
	
	private static final RGB BLACK = new RGB(0, 0, 0);
	
	/**
	 * ImageDescriptor for the "colorsquare" in the contextmenu
	 */
	private static class UnselectedColorDescriptor extends ImageDescriptor {
		
		protected final ImageData id;

		public UnselectedColorDescriptor(int color) {
			id = new ImageData(40, 20, 2, new PaletteData(new RGB[] {
					ColorPalette.getRGB(color, 0.2f), BLACK, BLACK, BLACK}));
			id.transparentPixel = 3;

			for (int i = 0; i < id.data.length; i += id.bytesPerLine) {
				for (int j = 0; j < 5; j++) {
					id.data[i + j] = (byte) 0xff;
				}
			}
		}

		@Override
		public ImageData getImageData() {
			return id;
		}
	}

	/**
	 * ImageDescriptor for the checked sign next to the colors in the contextmenu
	 */
	private static final class SelectedColorDescriptor extends	UnselectedColorDescriptor {
		public SelectedColorDescriptor(int color) {
			super(color);

			int offset = 6 * id.bytesPerLine;			
			for (int i = offset; i < id.data.length - offset; i += id.bytesPerLine) {
				id.data[i + 1] = (byte) 0xd5;
				id.data[i + 2] = (byte) 0x55;
				id.data[i + 3] = (byte) 0x7f;
			}
			id.data[offset + 1] = (byte) 0xfd;
			id.data[offset + 2] = (byte) 0x57;
			id.data[offset + 3] = (byte) 0xff;

			offset += id.bytesPerLine;
			id.data[offset + 1] = (byte) 0xf5;
			id.data[offset + 3] = (byte) 0xff;

			offset += 5 * id.bytesPerLine;
			id.data[offset + 1] = (byte) 0xf5;
			id.data[offset + 3] = (byte) 0xff;

			offset += id.bytesPerLine;
			id.data[offset + 1] = (byte) 0xfd;
			id.data[offset + 2] = (byte) 0x57;
			id.data[offset + 3] = (byte) 0xff;
		}
	}

	private final ImageDescriptor selectedColor, unselectedColor;

	public SetColorAction(GraphicalViewerImpl view,
			CollaborationView collaborationView, int index) {
		super(ColorPalette.getColorName(index), view, collaborationView, index);

		selectedColor = new SelectedColorDescriptor(index);
		unselectedColor = new UnselectedColorDescriptor(index);

		setImageDescriptor(unselectedColor);
	}
	
	@Override
	public void setChecked(boolean checked) {
		if (checked) {
			setImageDescriptor(selectedColor);
		} else {
			setImageDescriptor(unselectedColor);
		}
	}

	@Override
	protected boolean action(FeatureModel fm, String collName) {
		Feature feat = fm.getFeature(collName);
		if (feat != null) {
			if (feat.getColorList().getColor() != index) {
				feat.getColorList().setColor(index);
			} else {
				feat.getColorList().removeColor();
			}
			return true;
		}
		return false;
	}
}