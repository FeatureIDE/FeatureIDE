package de.ovgu.featureide.core.images;

import java.io.File;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;

import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;

/**
 * Images composer through images overlapping.
 * Images in the different feature folders need to have the same relative path to be combined.
 * 
 * @author Jabier Martinez
 *
 */
public class ImagesComposer extends ComposerExtensionClass {

	/**
	 * This is call when the project builds
	 * using the currently selected configuration by the user
	 */
	@Override
	public void performFullBuild(IFile config) {
		// Get the selected features and order them
		List<String> selectedFeatures = getSelectedNonAbstractFeatures(config);
		List<String> orderedFeatures = orderSelectedFeatures(selectedFeatures);

		// Default output folder
		File output = featureProject.getBuildFolder().getRawLocation().makeAbsolute().toFile();
		compose(orderedFeatures, output);
	}

	/**
	 * This is call when we want to generate all valid configurations or in other user actions
	 */
	@Override
	public void buildConfiguration(IFolder folder, Configuration configuration, String configurationName) {
		// call super to save the config file and others
		super.buildConfiguration(folder, configuration, configurationName);
		List<String> orderedFeatures = orderSelectedFeatures(configuration.getSelectedFeatureNames());

		// The output folder
		File output = new File(folder.getRawLocationURI());
		compose(orderedFeatures, output);
	}

	/**
	 * Compose and generate in the output folder
	 * 
	 * @param orderedFeatures
	 * @param output
	 */
	private void compose(List<String> orderedFeatures, File output) {
		// Create imagesMap, the key is the relative path from the feature
		// folder to the image file
		Map<String, List<File>> imagesMap = new LinkedHashMap<String, List<File>>();
		for (int i = 0; i < orderedFeatures.size(); i++) {
			IFolder f = featureProject.getSourceFolder().getFolder(orderedFeatures.get(i));
			File folder = f.getRawLocation().makeAbsolute().toFile();
			List<File> files = ImagesComposerUtils.getAllFiles(folder);
			for (File file : files) {
				if (ImagesComposerUtils.getImageFormat(file.getName()) != null) {
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

			File outputImageFile = new File(output, entry.getKey());
			try {
				ImagesComposerUtils.overlapImages(entry.getValue(), outputImageFile);
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
	}

	/**
	 * Get selected non abstract features
	 * 
	 * @param config
	 * @return features
	 */
	protected List<String> getSelectedNonAbstractFeatures(IFile config) {
		List<String> selectedFeatures = new ArrayList<String>();
		final Configuration configuration = new Configuration(featureProject.getFeatureModel());
		FileHandler.load(Paths.get(config.getLocationURI()), configuration, ConfigurationManager.getFormat(config.getName()));
		for (IFeature f : configuration.getSelectedFeatures()) {
			if (!f.getStructure().isAbstract()) {
				selectedFeatures.add(f.getName());
			}
		}
		return selectedFeatures;
	}

	/**
	 * Order the features in case of user-defined ordering
	 * 
	 * @param selectedFeatures
	 * @return ordered features
	 */
	protected List<String> orderSelectedFeatures(Collection<String> selectedFeatures) {
		// Order them if needed
		List<String> orderedFeatures = new ArrayList<String>();
		if (featureProject.getFeatureModel().isFeatureOrderUserDefined()) {
			List<String> featureOrderList = featureProject.getFeatureModel().getFeatureOrderList();
			for (String feature : featureOrderList) {
				if (selectedFeatures.contains(feature)) {
					orderedFeatures.add(feature);
				}
			}
		} else {
			orderedFeatures.addAll(selectedFeatures);
		}
		return orderedFeatures;
	}

}

