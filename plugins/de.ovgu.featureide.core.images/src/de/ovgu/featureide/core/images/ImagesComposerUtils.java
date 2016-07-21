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
		int i = name.lastIndexOf('.');
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
		List<BufferedImage> images = new ArrayList<BufferedImage>();
		int maxWidth = 0;
		int maxHeight = 0;
		for (File imageFile : imageFiles) {
			BufferedImage image = ImageIO.read(imageFile);
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
			BufferedImage combined = new BufferedImage(maxWidth, maxHeight, BufferedImage.TYPE_INT_ARGB);
			Graphics g = combined.getGraphics();
			for (BufferedImage i : images) {
				g.drawImage(i, 0, 0, null);
			}
			g.dispose();
			outputImageFile.getParentFile().mkdirs();
			String imageFormat = getImageFormat(outputImageFile.getName());
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

		for (File file : dir.listFiles()) {
			getAllFiles(files, file);
		}
		return files;
	}

}
