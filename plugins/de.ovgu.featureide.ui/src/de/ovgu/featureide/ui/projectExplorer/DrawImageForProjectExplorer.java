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
package de.ovgu.featureide.ui.projectExplorer;

import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.ui.ISharedImages;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Device;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.ImageData;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.color.ColorPalette;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * draws the images for the ProjectExplorer. The image includes the file-, folder- or package - image and the color of the feature.
 *
 *
 * @author Jonas Weigt
 */

public class DrawImageForProjectExplorer {

	private static final int NUMBER_OF_COLORS = 10;

	private static final Image JAVA_IMAGE = UIPlugin.getImage("JakFileIcon.png");
	private static final Image FOLDER_IMAGE = PlatformUI.getWorkbench().getSharedImages().getImage(org.eclipse.ui.ISharedImages.IMG_OBJ_FOLDER);
	private static final Image PACKAGE_IMAGE = JavaUI.getSharedImages().getImage(ISharedImages.IMG_OBJS_PACKAGE);
	private static final Image FILE_IMAGE = PlatformUI.getWorkbench().getSharedImages().getImage(org.eclipse.ui.ISharedImages.IMG_OBJ_FILE);

	private static final Device DEVICE = FOLDER_IMAGE.getDevice();
	private static final int ICON_HEIGHT = FOLDER_IMAGE.getBounds().height;
	private static final int ICON_WIDTH = FOLDER_IMAGE.getBounds().width;

	/**
	 * constant for the width of the single colorImage
	 */
	private final static int COLOR_IMAGE_WIDTH = (FOLDER_IMAGE.getBounds().width / 4) + 1;
	private static Image WHITESPACE_IMAGE;

	private final static Map<Integer, Image> COLOR_IMAGES = new HashMap<>();

	public enum ExplorerObject {
		JAVA_FILE(1), FOLDER(2), PACKAGE(3), FILE(4);

		final int value;

		private ExplorerObject(int value) {
			this.value = value;
		}
	}

	/**
	 * Cache for generated images.
	 */
	private final static Map<Integer, Image> images = new HashMap<Integer, Image>();

	private static void init() {
		final ImageData imageData = FOLDER_IMAGE.getImageData();

		Image finalImage = new Image(DEVICE, COLOR_IMAGE_WIDTH, imageData.height);
		GC gc = new GC(finalImage);
		gc.setForeground(new Color(DEVICE, 0, 0, 0));
		gc.drawRectangle(0, 0, COLOR_IMAGE_WIDTH - 1, ICON_HEIGHT - 1);
		gc.setBackground(new Color(DEVICE, 255, 255, 254));// use 255 for trancparency
		gc.fillRectangle(1, 1, COLOR_IMAGE_WIDTH - 2, ICON_HEIGHT - 2);
		WHITESPACE_IMAGE = finalImage;
		gc.dispose();

		for (int i = 0; i < NUMBER_OF_COLORS; i++) {
			finalImage = new Image(DEVICE, COLOR_IMAGE_WIDTH, imageData.height);
			gc = new GC(finalImage);
			gc.setForeground(new Color(DEVICE, 0, 0, 0));
			gc.setBackground(ColorPalette.getColor(i, 0.4f));
			gc.fillRectangle(1, 1, COLOR_IMAGE_WIDTH - 2, ICON_HEIGHT - 2);
			gc.drawRectangle(0, 0, COLOR_IMAGE_WIDTH - 1, ICON_HEIGHT - 1);
			gc.dispose();
			COLOR_IMAGES.put(i, finalImage);
		}
	}

	/**
	 * @param explorerObject
	 * @param colors List of colors from de.ovgu.featureide.fm.core.annotation.ColorPalette
	 * @param superImage The default image (may be null)
	 * @return the image with the icon of the file, folder or package (explorerObject) and the color of the feature
	 */
	public static Image drawExplorerImage(ExplorerObject explorerObject, List<Integer> colors, List<Integer> parentColors, Image superImage) {

		if (WHITESPACE_IMAGE == null) {
			init();
		}

		Collections.sort(colors, new Comparator<Integer>() {

			@Override
			public int compare(Integer i0, Integer i1) {
				return i0.compareTo(i1);
			}
		});

		// create hash value
		if (superImage == null) {
			colors.add(explorerObject.value);
		} else {
			colors.add(superImage.getImageData().hashCode());
		}
		final Integer hashCode = colors.hashCode();
		if (images.containsKey(hashCode)) {
			return images.get(hashCode);
		}
		colors.remove(colors.size() - 1);

		Image icon = superImage;
		if (icon == null) {
			switch (explorerObject) {
			case JAVA_FILE:
				icon = JAVA_IMAGE;
				break;
			case FOLDER:
				icon = FOLDER_IMAGE;
				break;
			case PACKAGE:
				icon = PACKAGE_IMAGE;
				break;
			case FILE:
				icon = FILE_IMAGE;
				break;
			default:
				throw new RuntimeException(explorerObject + " not supported");
			}
		}

		Image image;
		GC gc;

		if (parentColors != null) {
			image = new Image(DEVICE, (icon.getBounds().width + 2 + (parentColors.size() * COLOR_IMAGE_WIDTH)) - parentColors.size(), ICON_HEIGHT);
			gc = new GC(image);

			gc.drawImage(icon, 0, 0);

			for (int i = 0; i < parentColors.size(); i++) {
				if (colors.contains(parentColors.get(i))) {
					gc.drawImage(getColorImage(parentColors.get(i)), (icon.getBounds().width + 1 + (COLOR_IMAGE_WIDTH * i)) - i, 0);
				} else {
					gc.drawImage(WHITESPACE_IMAGE, (icon.getBounds().width + 1 + (COLOR_IMAGE_WIDTH * i)) - i, 0);
				}
			}
		} else {
			image = new Image(DEVICE, (icon.getBounds().width + 2 + (colors.size() * COLOR_IMAGE_WIDTH)) - colors.size(), ICON_HEIGHT);
			gc = new GC(image);

			gc.drawImage(icon, 0, 0);

			for (int i = 0; i < colors.size(); i++) {
				gc.drawImage(getColorImage(colors.get(i)), (icon.getBounds().width + 1 + (COLOR_IMAGE_WIDTH * i)) - i, 0);
			}
		}

		final ImageData data = image.getImageData();
		data.transparentPixel = data.palette.getPixel(new RGB(255, 255, 255));
		gc.dispose();

		final Image finalImage = new Image(DEVICE, data);
		images.put(hashCode, finalImage);
		return finalImage;
	}

	/**
	 * @param colors: gets a list of Integer to create an Image with the color in the list
	 * @return the image for the featureHouseExplorer with the folderIcon as default and only one color
	 */
	public static Image getFOPModuleImage(List<Integer> colors) {
		colors.add(ExplorerObject.FOLDER.value);
		final Integer hashCode = colors.hashCode();
		if (images.containsKey(hashCode)) {
			return images.get(hashCode);
		}
		colors.remove(colors.size() - 1);

		final Image finalImage = new Image(DEVICE, FOLDER_IMAGE.getImageData().width + COLOR_IMAGE_WIDTH + 3, FOLDER_IMAGE.getImageData().height);
		final GC gc = new GC(finalImage);
		gc.drawImage(FOLDER_IMAGE, 0, 0);
		if (WHITESPACE_IMAGE == null) {
			init();
		}
		if (colors.get(0).equals(-1)) {
			gc.drawImage(WHITESPACE_IMAGE, ICON_WIDTH + 2, 0);
		} else {
			gc.drawImage(getColorImage(colors.get(0)), ICON_WIDTH + 2, 0);
		}
		final ImageData data = finalImage.getImageData();
		data.transparentPixel = data.palette.getPixel(new RGB(255, 255, 255));
		gc.dispose();
		final Image image = new Image(DEVICE, data);
		images.put(hashCode, image);
		return image;
	}

	/**
	 * @param colorID gets a list of Integer to create an Image with the colors in the list
	 * @return a colored image with the original colors from de.ovgu.featureide.fm.core.annotation.ColorPalette
	 */
	private static Image getColorImage(int colorID) {
		return COLOR_IMAGES.get(colorID);
	}

	public static Image getPackageImage() {
		return PACKAGE_IMAGE;
	}

}
