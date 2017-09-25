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
package de.ovgu.featureide.core.images;

import java.awt.Graphics;
import java.awt.image.BufferedImage;
import java.io.File;
import java.util.ArrayList;
import java.util.List;

import javax.imageio.ImageIO;

/**
 * Images composer utils
 *
 * @author Jabier Martinez
 */
public class ImagesComposerUtils {

	/**
	 * The main file formats supported by javax.imageio
	 *
	 * @param name
	 * @return null if it is not an image file or the file format
	 */
	public static String getImageFormat(String name) {
		final int i = name.lastIndexOf('.');
		if (i > 0) {
			name = name.substring(i + 1);
		} else {
			return null;
		}
		if (name.equalsIgnoreCase("gif")) {
			return "GIF";
		} else if (name.equalsIgnoreCase("png")) {
			return "PNG";
		} else if (name.equalsIgnoreCase("jpg")) {
			return "JPEG";
		} else if (name.equalsIgnoreCase("jpeg")) {
			return "JPEG";
		} else if (name.equalsIgnoreCase("bmp")) {
			return "BMP";
		}
		return null;
	}

	/**
	 * Overlap a list of images in order (The first one will be at the background)
	 *
	 * @param image files
	 * @param output image file
	 * @throws Exception
	 */
	public static void overlapImages(List<File> imageFiles, File outputImageFile) throws Exception {
		// Get the images and calculate final size
		final List<BufferedImage> images = new ArrayList<BufferedImage>();
		int maxWidth = 0;
		int maxHeight = 0;
		for (final File imageFile : imageFiles) {
			final BufferedImage image = ImageIO.read(imageFile);
			if (image == null) {
				throw new Exception("Error reading image: " + imageFile.getAbsolutePath());
			}
			if (image.getWidth() > maxWidth) {
				maxWidth = image.getWidth();
			}
			if (image.getHeight() > maxHeight) {
				maxHeight = image.getHeight();
			}
			images.add(image);
		}

		// Overlap the images
		if (!images.isEmpty()) {
			final BufferedImage combined = new BufferedImage(maxWidth, maxHeight, BufferedImage.TYPE_INT_ARGB);
			final Graphics g = combined.getGraphics();
			for (final BufferedImage i : images) {
				g.drawImage(i, 0, 0, null);
			}
			g.dispose();
			outputImageFile.getParentFile().mkdirs();
			final String imageFormat = getImageFormat(outputImageFile.getName());
			ImageIO.write(combined, imageFormat, outputImageFile);
		}
	}

	/**
	 * Get all files recursively
	 *
	 * @param dir
	 * @return files
	 */
	public static List<File> getAllFiles(File dir) {
		return getAllFiles(null, dir);
	}

	/**
	 * getAllFiles recursively, initialize files with null
	 *
	 * @param files
	 * @param dir
	 * @return
	 */
	private static List<File> getAllFiles(List<File> files, File dir) {
		if (files == null) {
			files = new ArrayList<File>();
		}

		if (!dir.isDirectory()) {
			files.add(dir);
			return files;
		}

		for (final File file : dir.listFiles()) {
			getAllFiles(files, file);
		}
		return files;
	}

}
