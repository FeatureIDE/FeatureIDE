/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.base.impl;

import javax.annotation.CheckForNull;
import javax.annotation.Nonnull;

import de.ovgu.featureide.fm.core.CoreExtensionLoader;
import de.ovgu.featureide.fm.core.ExtensionManager;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;

/**
 * Manages additional formats for a certain object (e.g., a feature model or configuration).
 * 
 * @author Sebastian Krieter
 */
public class FormatManager<T extends IPersistentFormat<?>> extends ExtensionManager<T> {

	@SuppressWarnings("unchecked")
	public FormatManager(T... formats) {
		setExtensionLoaderInternal(new CoreExtensionLoader<T>(formats));
	}

	protected FormatManager() {
	}

	/**
	 * Extracts the file extension from a file name.<br/>
	 * <b>Note:</b> A dot at the first position of the file name is ignored.
	 * E.g., ".file" has no extension, but ".file.txt" would return "txt".
	 * 
	 * @param fileName the name of a file
	 * @return the extension or an empty string if there is none.
	 */
	@Nonnull
	public static String getFileExtension(String fileName) {
		final int extIndex = fileName.lastIndexOf('.');
		return extIndex > 0 ? fileName.substring(extIndex + 1) : "";
	}

	public T getFormatById(String id) throws NoSuchExtensionException {
		return getExtension(id);
	}

	/**
	 * Returns the format that fits the given parameter.
	 * 
	 * @param fileName the file name (it is also possible to just specify the file extension (e.g., "xml"))
	 * @return A {@link IPersistentFormat format} that uses the given extension or {@code null} if there is none.<br/>
	 *         In case there are multiple formats that fit the given extension, only the first one of the list is returned.
	 *         In order to avoid this, please use the methods {@link #getFormatByContent(CharSequence, String)} or {@link #getFormatByPath(CharSequence)}, which
	 *         also take into account the content that should be parsed.
	 */
	@CheckForNull
	public T getFormatByFileName(String fileName) {
		if (fileName != null) {
			final String extension = getFileExtension(fileName);
			for (T format : getExtensions()) {
				if (extension.equals(format.getSuffix())) {
					return format;
				}
			}
		}
		return null;
	}

	@CheckForNull
	public T getFormatByContent(CharSequence content) {
		for (T format : getExtensions()) {
			if (format.supportsContent(content)) {
				return format;
			}
		}
		return null;
	}

	public T getFormatByContent(CharSequence content, String fileName) {
		if (fileName != null) {
			final String extension = getFileExtension(fileName);
			for (T format : getExtensions()) {
				if (extension.equals(format.getSuffix()) && format.supportsContent(content)) {
					return format;
				}
			}
		}
		return null;
	}

}
