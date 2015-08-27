/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.ImageData;
import org.eclipse.jdt.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.annotation.ColorPalette;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * draws the images for the ProjectExplorer.
 * The image includes the file-, folder- or package - image
 * and the color of the feature.
 * 
 * 
 * @author Jonas Weigt
 */

public class DrawImageForProjectExplorer {
	public static final String ID = UIPlugin.PLUGIN_ID + ".editors.JavaEditor";
	private static final Image JAVA_IMAGE = UIPlugin
			.getImage("JakFileIcon.png");

	public enum ExplorerObject {
		FILE, FOLDER, PACKAGE;
	}
	
	/**
	 * constant for the width of the single colorImage
	 */
	final static int WIDTHCONSTANT = 4;

	private final static Map<Integer, Image> images = new HashMap<Integer, Image>();

	/**
	 * @param explorerObject
	 * @param colors List of colors from de.ovgu.featureide.fm.core.annotation.ColorPalette
	 * @return the image with the icon of the file, folder or package (explorerObject) and the color of the feature
	 */
	public static Image drawExplorerImage(ExplorerObject explorerObject, List<Integer> colors) {
		colors.sort(new Comparator<Integer>() {

			@Override
			public int compare(Integer i0, Integer i1) {
				return i0.compareTo(i1);
			}
		});
		// create hash value
		switch (explorerObject) {
		case FILE:
			colors.add(1);
			break;
		case FOLDER:
			colors.add(2);
			break;
		case PACKAGE:
			colors.add(3);
			break;
		default:
			throw new RuntimeException(explorerObject + " not implemented");
		}
		Integer hashCode = colors.hashCode();
		if (images.containsKey(hashCode)) {
			return images.get(hashCode);
		}
		colors.remove(colors.size() - 1);

		Image dummyImage = PlatformUI.getWorkbench().getSharedImages().getImage(org.eclipse.ui.ISharedImages.IMG_OBJ_FOLDER);
		Image finalImage = new Image(dummyImage.getDevice(), dummyImage.getImageData().width +42, dummyImage.getImageData().height);
		ImageData data = null;
		org.eclipse.swt.graphics.GC gc = new org.eclipse.swt.graphics.GC(finalImage);

		ArrayList<Image> liste = new ArrayList<>();
		Image icon = null;
		switch (explorerObject) {
		case FILE:
			icon = JAVA_IMAGE;
			break;
		case FOLDER:
			icon = PlatformUI.getWorkbench().getSharedImages().getImage(org.eclipse.ui.ISharedImages.IMG_OBJ_FOLDER);
			break;
		case PACKAGE:
			icon = JavaUI.getSharedImages().getImage(ISharedImages.IMG_OBJS_PACKAGE);
			break;
		}

		gc.drawImage(icon, 0, 0);
		liste.add(icon);
		
		for (int i = 0; i < 10; i++) {
			if (colors.contains(i)) {
				gc.drawImage(getColorImage(i), 17 + WIDTHCONSTANT * i, 0);
			} else {
				gc.drawImage(getWhiteImage(), 17 + WIDTHCONSTANT * i, 0);
			}
		}
		gc.setForeground(new Color(liste.get(0).getDevice(), 0, 0, 0));
		gc.drawLine(57, 0, 57, 21); //draws the last vertical line
		gc.drawLine(17, 15, 57, 15);//draws the horizontal line
		data = finalImage.getImageData();
		gc.dispose();
		Image image = new Image(liste.get(0).getDevice(), data);
		images.put(hashCode, image);
		return image;
	}

	/**
	 * @param colors: gets a list of Integer to create an Image with the color in the list
	 * @return the image for the featureHouseExplorer with the folderIcon as default and only one color
	 */
	public static Image drawFeatureHouseExplorerImage(List<Integer> colors) {
		colors.add(2);
		Integer hashCode = colors.hashCode();
		if (images.containsKey(hashCode)) {
			return images.get(hashCode);
		}
		colors.remove(colors.size() - 1);

		Image dummyImage = PlatformUI.getWorkbench().getSharedImages().getImage(org.eclipse.ui.ISharedImages.IMG_OBJ_FOLDER);
		Image finalImage = new Image(dummyImage.getDevice(), dummyImage.getImageData().width + 6, dummyImage.getImageData().height);
		ImageData data = null;
		org.eclipse.swt.graphics.GC gc = new org.eclipse.swt.graphics.GC(finalImage);

		Image folderImage = PlatformUI.getWorkbench().getSharedImages().getImage(org.eclipse.ui.ISharedImages.IMG_OBJ_FOLDER);
		gc.drawImage(folderImage, 0, 0);

		if (colors.get(0).equals(-1)) {
			gc.drawImage(getWhiteImage(), 17, 0);
			gc.setForeground(new Color(folderImage.getDevice(), 0, 0, 0));
			gc.drawLine(21, 0, 21, 16);//draws the last vertical line
			gc.drawLine(17, 15, 21, 15);//draws the horizontal line
			data = finalImage.getImageData();
			gc.dispose();
			Image image = new Image(dummyImage.getDevice(), data);
			images.put(hashCode, image);

			return image;
		}
		gc.drawImage(getColorImage(colors.get(0)), 17, 0);
		gc.setForeground(new Color(folderImage.getDevice(), 0, 0, 0));
		gc.drawLine(21, 0, 21, 16);//draws the last vertical line
		gc.drawLine(17, 15, 21, 15);//draws the horizontal line
		data = finalImage.getImageData();
		gc.dispose();
		Image image = new Image(dummyImage.getDevice(), data);
		images.put(hashCode, image);

		return image;
	}

	/**
	 * @return a white image, is needed to fill the parts, where no color is selected
	 */
	public static Image getWhiteImage() {
		Image folderImage = PlatformUI.getWorkbench().getSharedImages().getImage(org.eclipse.ui.ISharedImages.IMG_OBJ_FOLDER);
		Image finalImage = new Image(folderImage.getDevice(), folderImage.getImageData().width / 4, folderImage.getImageData().height);
		ImageData data = null;
		org.eclipse.swt.graphics.GC gc = new org.eclipse.swt.graphics.GC(finalImage);
		gc.setForeground(new Color(folderImage.getDevice(), 0, 0, 0));
		gc.drawRectangle(0, 0, folderImage.getImageData().width / 4, folderImage.getImageData().height);

		gc.setBackground(new Color(folderImage.getDevice(), 255, 255, 255));
		gc.fillRectangle(1, 1, (folderImage.getImageData().width / 4) - 1, (folderImage.getImageData().height) - 1);
		data = finalImage.getImageData();
		gc.dispose();
		return new Image(finalImage.getDevice(), data);

	}

	/**
	 * @param colorID gets a list of Integer to create an Image with the colors in the list
	 * @return a colored image with the original colors from
	 *         de.ovgu.featureide.fm.core.annotation.ColorPalette
	 */
	public static Image getColorImage(int colorID) {
		Image folderImage = PlatformUI.getWorkbench().getSharedImages().getImage(org.eclipse.ui.ISharedImages.IMG_OBJ_FOLDER);
		Image finalImage = new Image(folderImage.getDevice(), folderImage.getImageData().width / 4, folderImage.getImageData().height);
		ImageData data = null;
		org.eclipse.swt.graphics.GC gc = new org.eclipse.swt.graphics.GC(finalImage);
		gc.setForeground(new Color(folderImage.getDevice(), 0, 0, 0));
		gc.drawRectangle(0, 0, folderImage.getImageData().width / 4, folderImage.getImageData().height);

		gc.setBackground(ColorPalette.getColor(colorID, 0.4f));
		gc.fillRectangle(1, 1, (folderImage.getImageData().width / 4) - 1, (folderImage.getImageData().height) - 1);
		data = finalImage.getImageData();
		gc.dispose();
		return new Image(finalImage.getDevice(), data);

	}

}
