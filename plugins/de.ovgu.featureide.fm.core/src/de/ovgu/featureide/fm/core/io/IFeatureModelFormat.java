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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.core.io;

import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Format for {@link IFeatureModel feature models}.
 *
 * @author Sebastian Krieter
 * @author Johannes Herschel
 */
public interface IFeatureModelFormat extends IPersistentFormat<IFeatureModel>, IFeatureNameValidator {

	public static String extensionPointID = "FMFormat";

	public static String extensionID = "fmFormat";

	@Override
	String getName();

	void setFeatureNameValidator(IFeatureNameValidator validator);

	IFeatureNameValidator getFeatureNameValidator();

	@Override
	default boolean isValidFeatureName(String featureName) {
		return true;
	}

	/**
	 * Computes the name of an imported model from its file path. The default implementation removes the file extension (if present) and replaces directory
	 * separators with dots.
	 *
	 * @param path The file path of the imported model
	 * @return The name of the import
	 */
	default String getImportNameFromPath(String path) {
		// Remove file extension
		final int fileExtensionIndex = path.lastIndexOf(".");
		final String removedExtension = fileExtensionIndex != -1 ? path.substring(0, fileExtensionIndex) : path;
		// Replace / and \ by .
		return removedExtension.replaceAll("[/\\\\]", ".");
	}

	/**
	 * Checks whether the given name is valid for an imported model in this format. The default implementation returns <code>true</code> for any name.
	 *
	 * @param name The import name to check
	 * @return <code>true</code> iff the given name is valid in this format
	 */
	default boolean isValidImportName(String name) {
		return true;
	}

	/**
	 * Checks whether the given alias is valid for an imported model in this format. The default implementation returns <code>true</code> for any alias.
	 *
	 * @param alias The import alias to check
	 * @return <code>true</code> iff the given alias is valid in this format
	 */
	default boolean isValidImportAlias(String alias) {
		return true;
	}
}
