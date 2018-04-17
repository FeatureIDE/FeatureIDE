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
package de.ovgu.featureide.fm.core;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Manages all extension of a certain extension point.
 *
 * @author Sebastian Krieter
 */
// TODO Check synchronization for get and add extension methods
public class ExtensionManager<T extends de.ovgu.featureide.fm.core.IExtension> {

	public static class NoSuchExtensionException extends Exception {

		private static final long serialVersionUID = -8143277745205866068L;

		public NoSuchExtensionException(String message) {
			super(message);
		}
	}

	private final List<T> extensions = new ArrayList<>();

	private IExtensionLoader<T> extensionLoader;

	protected void setExtensionLoaderInternal(IExtensionLoader<T> extensionLoader) {
		this.extensionLoader = extensionLoader;
	}

	public boolean addExtension(T extension) {
		for (final T t : extensions) {
			if (t.getId().equals(extension.getId())) {
				return false;
			}
		}
		extensions.add(extension);
		return true;
	}

	public synchronized List<T> getExtensions() {
		if (extensionLoader != null) {
			synchronized (extensions) {
				if (extensionLoader != null) {
					extensionLoader.loadProviders(this);
					extensionLoader = null;
				}
			}
		}
		return Collections.unmodifiableList(extensions);
	}

	public T getExtension(String id) throws NoSuchExtensionException {
		java.util.Objects.requireNonNull(id, "ID must not be null!");

		for (final T extension : getExtensions()) {
			if (id.equals(extension.getId())) {
				return extension;
			}
		}
		throw new NoSuchExtensionException("No extension found for ID " + id);
	}

}
