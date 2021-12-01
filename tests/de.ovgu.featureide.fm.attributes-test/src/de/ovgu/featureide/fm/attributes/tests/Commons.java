/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.attributes.tests;

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.FileFilter;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.DefaultFeatureModelFactory;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;

/**
 * A class containing numerous methods that are needed for many tests, especially those assessing files.
 *
 * @author Marcus Pinnecke
 * @author Thomas Thuem
 * @author Joshua Sprey
 */
public class Commons {

	public static File getRemoteOrLocalFolder(String path) {
		final File folder = new File("src/" + path);
		return folder;
	}

	public static final String TEST_FEATURE_MODEL_PATH = "extendedTestFeatureModels/";

	public final static IFeatureModel loadTestExtendedFeatureModelFromFile(final String filename) {
		return loadFeatureModelFromFile(filename, getRemoteOrLocalFolder(TEST_FEATURE_MODEL_PATH));
	}

	/**
	 * Loads a feature model from the file <code>featureModelXmlFilename</code> from a given <code>remotePath</code>, or if <code>remotePath</code> is not
	 * available, from <code>localClassPath</code>. The search for the file excludes files that don't have the same file extension as
	 * <code>featureModelXmlFilename</code>.
	 *
	 * @param filename Feature model file, e.g., "model.xml"
	 * @param remotePath Directory in which the model is located, e.g., "/myremote_server_path/models"
	 * @param localClassPath Alternative resource path in class path to look for the feature model file, if remote path is not available (in local mode for
	 *        instance).
	 * @return Feature model loaded from the given file
	 */
	public final static IFeatureModel loadFeatureModelFromFile(final String filename, final File modelFolder) {
		return loadFeatureModelFromFile(filename, new FileFilterByExtension(extractFileExtension(filename)), modelFolder);
	}

	/**
	 * Extracts the file extension of the given file <b>filename</b> or empty string, if no file extension is available. The extension does not include the
	 * leading ".".
	 *
	 * @param filename file name
	 * @return File extension or empty string
	 */
	public static String extractFileExtension(String filename) {
		final int position = filename.lastIndexOf('.');
		if (position > 0) {
			return filename.substring(position + 1);
		} else {
			return "";
		}
	}

	/**
	 * Loads a feature model from the file <code>featureModelXmlFilename</code> from a given <code>remotePath</code>, or if <code>remotePath</code> is not
	 * available, from <code>localClassPath</code>. The search for the file excludes files that have the extension specified with <b>filter</b>.
	 * <code>featureModelXmlFilename</code>.
	 *
	 * @see {@link #loadFeatureModelFromFile(String, String, String) load model with extension equal to featureModelXmlFilename}
	 * @param featureModelXmlFilename Feature model file, e.g., "model.xml"
	 * @param remotePath Directory in which the model is located, e.g., "/myremote_server_path/models"
	 * @param localClassPath Alternative resource path in class path to look for the feature model file, if remote path is not available (in local mode for
	 *        instance).
	 * @return Feature model loaded from the given file
	 */
	public final static IFeatureModel loadFeatureModelFromFile(final String featureModelXmlFilename, final FileFilter filter, final File modelFolder) {
		for (final File f : modelFolder.listFiles(filter)) {
			if (f.getName().equals(featureModelXmlFilename)) {
				return FeatureModelManager.load(f.toPath());
			}
		}
		return DefaultFeatureModelFactory.getInstance().create();
	}

	public final static <T> String join(T delimiter, List<T> list) {
		final StringBuilder sb = new StringBuilder();
		if ((list != null) && !list.isEmpty()) {
			for (int i = 0; i < list.size(); i++) {
				sb.append(list.get(i));
				if (i <= (list.size() - 1)) {
					sb.append(delimiter);
				}
			}
		}
		return sb.toString();
	}

	/**
	 * File filter that accepts files which extension is equal to the extension.
	 *
	 * @author Marcus Pinnecke
	 */
	public static class FileFilterByExtension implements FileFilter {

		final String fileExtension;

		/**
		 * File filter that accepts files which extension is equal to the given extension.
		 *
		 * @param fileExtension file extension that should be accepted (e.g., "xml")
		 */
		public FileFilterByExtension(final String fileExtension) {
			assert ((fileExtension != null) && !fileExtension.isEmpty());

			this.fileExtension = fileExtension;
		}

		@Override
		public boolean accept(final File pathname) {
			return pathname.getName().endsWith("." + fileExtension);
		}
	};

	public static ExtendedFeatureModel getBaseModel() {
		IFeatureModel model = Commons.loadTestExtendedFeatureModelFromFile("BaseExtendedFeatureModel.xml");
		assertTrue(model instanceof ExtendedFeatureModel);
		return (ExtendedFeatureModel) model;
	}

	public static ExtendedFeatureModel getSandwitchModel() {
		IFeatureModel model = Commons.loadTestExtendedFeatureModelFromFile("SandwichModel.xml");
		assertTrue(model instanceof ExtendedFeatureModel);
		return (ExtendedFeatureModel) model;
	}

	public static ExtendedFeatureModel getNewFormatBikeModel() {
		IFeatureModel model = Commons.loadTestExtendedFeatureModelFromFile("newFormatBike.xml");
		assertTrue(model instanceof ExtendedFeatureModel);
		return (ExtendedFeatureModel) model;
	}

	public static boolean compareByAttributeValues(ExtendedFeatureModel model1, ExtendedFeatureModel model2) {
		return compareModelToValueMap(model2, extractValueMap(model1));
	}

	public static Map<String, Map<String, Object>> extractValueMap(ExtendedFeatureModel model) {
		Map<String, Map<String, Object>> valueMap = new HashMap<>();
		for (IFeature feat : model.getFeatures()) {
			ExtendedFeature ext = (ExtendedFeature) feat;
			Map<String, Object> featValueMap = new HashMap<>();
			for (IFeatureAttribute att : ext.getAttributes()) {
				featValueMap.put(att.getName(), att.getValue());
			}
			valueMap.put(ext.getName(), featValueMap);

		}

		return valueMap;
	}

	public static boolean compareModelToValueMap(ExtendedFeatureModel model, Map<String, Map<String, Object>> valueMap) {
		for (IFeature feat : model.getFeatures()) {
			ExtendedFeature ext = (ExtendedFeature) feat;
			if (!valueMap.containsKey(ext.getName())) {
				return false;
			}
			for (IFeatureAttribute att : ext.getAttributes()) {
				if (valueMap.get(ext.getName()).containsKey(att.getName())) {
					if (att.getValue() == null) {
						if (valueMap.get(ext.getName()).get(att.getName()) == null) {
							continue;
						}
						return false;
					}
					if (valueMap.get(ext.getName()).get(att.getName()) == null) {
						return false;
					}
					if (!valueMap.get(ext.getName()).get(att.getName()).equals(att.getValue())) {
						return false;
					}
				} else {
					return false;
				}
			}

		}
		return true;
	}

}
