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
package de.ovgu.featureide.fm.core.base.impl;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.LinkedList;
import java.util.List;

import javax.annotation.CheckForNull;

import de.ovgu.featureide.fm.core.CoreExtensionLoader;
import de.ovgu.featureide.fm.core.ExtensionManager;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.LazyReader;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;

/**
 * Manages additional formats for a certain object (e.g., a feature model or configuration).
 *
 * @author Sebastian Krieter
 */
public class FormatManager<T extends IPersistentFormat<?>> extends ExtensionManager<T> {

	@SafeVarargs
	public FormatManager(Class<? extends T>... formats) {
		setExtensionLoaderInternal(new CoreExtensionLoader<T>(formats));
	}

	protected FormatManager() {}

	public T getFormatById(String id) throws NoSuchExtensionException {
		return getExtension(id);
	}

	public boolean hasFormat(Path file) {
		return getFormatByContent(file) != null;
	}

	/**
	 * Returns the format that fits the given parameter.
	 *
	 * @param content the file's content
	 * @param fileName the file name
	 * @return A {@link IPersistentFormat format} that uses the given extension or {@code null} if there is none.<br/> In case there are multiple formats that
	 *         fit the given extension, only the first one of the list is returned. In order to avoid this, please use the methods
	 *         {@link #getFormatByContent(CharSequence, String)} or {@link #getFormatByPath(CharSequence)}, which also take into account the content that should
	 *         be parsed.
	 */
	@CheckForNull
	public T getFormatByContent(CharSequence content, String fileName) {
		if (fileName != null) {
			final String extension = SimpleFileHandler.getFileExtension(fileName);
			for (final T format : getExtensions()) {
				if (extension.equals(format.getSuffix()) && format.supportsContent(content)) {
					return format;
				}
			}
		}
		return null;
	}

	public T getFormatByContent(Path path) {
		if (path != null) {
			final String extension = SimpleFileHandler.getFileExtension(path);
			final List<T> formatList = new LinkedList<>();
			for (final T format : getExtensions()) {
				if (extension.equals(format.getSuffix())) {
					formatList.add(format);
				}
			}
			if (!formatList.isEmpty()) {
				try (InputStream inputStream = Files.newInputStream(path, StandardOpenOption.SYNC, StandardOpenOption.READ)) {
					final LazyReader lazyReader = new LazyReader(inputStream);
					for (final T format : formatList) {
						if (extension.equals(format.getSuffix()) && format.supportsContent(lazyReader)) {
							return format;
						}
					}
				} catch (final IOException e) {
					Logger.logError(e);
					return formatList.get(0);
				}
			}
		}
		return null;
	}

}
