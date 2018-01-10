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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide;

import java.io.File;
import java.io.FileFilter;
import java.util.List;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;

/**
 * A class containing numerous methods that are needed for many tests, especially those assessing files.
 *
 * @author Marcus Pinnecke
 * @author Thomas Thuem
 */
public class Commons {

	public static File getRemoteOrLocalFolder(String path) {
		final File folder = new File("src/" + path);
		return folder;
	}

	private static final String BENCHMARK_FEATURE_MODEL_PATH = "benchmarkFeatureModels/";

	private static final String TEST_FEATURE_MODEL_PATH = "testFeatureModels/";

	public final static IFeatureModel loadBenchmarkFeatureModelFromFile(final String filename) {
		return loadFeatureModelFromFile(filename, getRemoteOrLocalFolder(BENCHMARK_FEATURE_MODEL_PATH));
	}

	public final static IFeatureModel loadTestFeatureModelFromFile(final String filename) {
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
				return FeatureModelManager.load(f.toPath()).getObject();
			}
		}
		return FMFactoryManager.getEmptyFeatureModel();
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

}
