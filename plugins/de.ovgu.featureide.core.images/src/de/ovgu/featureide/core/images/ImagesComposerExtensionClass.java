package de.ovgu.featureide.core.images;

import java.awt.Graphics;
import java.awt.image.BufferedImage;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import javax.imageio.ImageIO;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;

import de.ovgu.featureide.core.builder.ComposerExtensionClass;

/**
 * Images composer through images overlapping.
 * Images in the different feature folders need to have the same relative path to be combined.
 * 
 * @author Jabier Martinez
 *
 */
public class ImagesComposerExtensionClass extends ComposerExtensionClass {

	@Override
	public Mechanism getGenerationMechanism() {
		return null;
	}

	@Override
	public void performFullBuild(IFile config) {
		try {
			List<IFolder> selectedFeatures = getSelectedFeatures(config);
			List<IFolder> orderedFeatures = orderSelectedFeatures(selectedFeatures);

			// Create imagesMap, the key is the relative path from the feature
			// folder to the image file
			Map<String, List<File>> imagesMap = new LinkedHashMap<String, List<File>>();
			for (int i = 0; i < orderedFeatures.size(); i++) {
				IFolder f = orderedFeatures.get(i);
				File folder = f.getRawLocation().makeAbsolute().toFile();
				List<File> files = getAllFiles(folder);
				for (File file : files) {
					if (getImageFormat(file.getName()) != null) {
						String relative = folder.toURI().relativize(file.toURI()).getPath();
						List<File> currentList = imagesMap.get(relative);
						if (currentList == null) {
							currentList = new ArrayList<File>();
						}
						currentList.add(file);
						imagesMap.put(relative, currentList);
					}
				}
			}

			// For each image, combine the related image files
			for (Entry<String, List<File>> entry : imagesMap.entrySet()) {

				List<BufferedImage> images = new ArrayList<BufferedImage>();
				int maxWidth = 0;
				int maxHeight = 0;

				for (File imageFile : entry.getValue()) {
					BufferedImage image = ImageIO.read(imageFile);
					if (image.getWidth() > maxWidth) {
						maxWidth = image.getWidth();
					}
					if (image.getHeight() > maxHeight) {
						maxHeight = image.getHeight();
					}
					images.add(image);
				}

				if (!images.isEmpty()) {
					BufferedImage combined = new BufferedImage(maxWidth, maxHeight, BufferedImage.TYPE_INT_ARGB);
					Graphics g = combined.getGraphics();
					for (BufferedImage i : images) {
						g.drawImage(i, 0, 0, null);
					}
					g.dispose();
					File output = featureProject.getBuildFolder().getRawLocation().makeAbsolute().toFile();
					File outputImageFile = new File(output, entry.getKey());
					outputImageFile.getParentFile().mkdirs();
					ImageIO.write(combined, getImageFormat(entry.getKey()), outputImageFile);
				}
			}

		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	/**
	 * The main file formats supported by javax.imageio
	 * 
	 * @param name
	 * @return null if it is not an image file or the file format
	 */
	private String getImageFormat(String name) {
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
	 * Order the features in case of user-defined ordering
	 * 
	 * @param selectedFeatures
	 * @return ordered features
	 */
	private List<IFolder> orderSelectedFeatures(List<IFolder> selectedFeatures) {
		// Order them if needed
		Collection<String> featureOrderList = featureProject.getFeatureModel().getFeatureOrderList();
		if (featureOrderList != null && !featureOrderList.isEmpty()) {
			List<IFolder> orderedFeatures = new ArrayList<IFolder>();
			for (String feature : featureOrderList) {
				IFolder folder = featureProject.getSourceFolder().getFolder(feature);
				if (selectedFeatures.contains(folder)) {
					orderedFeatures.add(folder);
				}
			}
			return orderedFeatures;
		}
		return selectedFeatures;
	}

	/**
	 * Get selected features
	 * 
	 * @param config
	 * @return list of IFolders of the features
	 * @throws FileNotFoundException
	 * @throws IOException
	 */
	private List<IFolder> getSelectedFeatures(IFile config) throws FileNotFoundException, IOException {
		List<IFolder> selectedFeatures = new ArrayList<IFolder>();
		BufferedReader reader = null;
		if (config != null) {
			try {
				reader = new BufferedReader(
						new InputStreamReader(new FileInputStream(config.getRawLocation().toFile()), Charset.availableCharsets().get("UTF-8")));
				String line = null;
				while ((line = reader.readLine()) != null) {
					if (line.startsWith("#"))
						continue;
					IFolder f = featureProject.getSourceFolder().getFolder(line);
					if (f != null) {
						if (!selectedFeatures.contains(f)) {
							selectedFeatures.add(f);
						}
					}
				}
			} finally {
				if (reader != null) {
					reader.close();
				}
			}
		}
		return selectedFeatures;
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
