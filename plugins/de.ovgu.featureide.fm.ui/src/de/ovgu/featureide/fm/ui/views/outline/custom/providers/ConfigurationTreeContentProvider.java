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
package de.ovgu.featureide.fm.ui.views.outline.custom.providers;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.viewers.Viewer;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.EclipseFileSystem;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry;
import de.ovgu.featureide.fm.ui.views.outline.computations.ConfigurationOutlineStandardBundle;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineTreeContentProvider;

/**
 * TODO description
 *
 * @author Chico Sundermann
 */
public class ConfigurationTreeContentProvider extends OutlineTreeContentProvider {

	private static final String ENTRY_EXTENSION_ID = "de.ovgu.featureide.fm.ui.ConfigurationOutlineEntry";

	private Configuration config;

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		if (newInput != null) {
			if (newInput instanceof Configuration) {
				config = ((Configuration) newInput);
			} else if (newInput instanceof IFile) {
				final IFile iFile = (IFile) newInput;
				if (iFile.exists()) {
					final Path filePath = EclipseFileSystem.getPath(iFile);
					if (ConfigurationManager.isFileSupported(filePath)) {
						config = ConfigurationManager.getInstance(filePath).getObject();
					}
				}
			}
		}
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.OutlineTreeContentProvider#getElements(java.lang.Object)
	 */
	@Override
	public Object[] getElements(Object inputElement) {
		if (config != null) {
			final List<IOutlineEntry> topLevelEntries = new ArrayList<>();
			topLevelEntries.add(new ConfigurationOutlineStandardBundle(config));
			topLevelEntries.addAll(getExtensionEntries());
			return topLevelEntries.toArray();
		}
		return new String[] { "Config not initialized yet" };
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.OutlineTreeContentProvider#getChildren(java.lang.Object)
	 */
	@Override
	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof IOutlineEntry) {
			final IOutlineEntry entry = (IOutlineEntry) parentElement;
			if (entry.hasChildren()) {
				return entry.getChildren().toArray();
			}
		}
		return null;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.OutlineTreeContentProvider#getParent(java.lang.Object)
	 */
	@Override
	public Object getParent(Object element) {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.OutlineTreeContentProvider#hasChildren(java.lang.Object)
	 */
	@Override
	public boolean hasChildren(Object element) {
		if (element instanceof IOutlineEntry) {
			return ((IOutlineEntry) element).hasChildren();
		}
		return false;
	}

	private List<IOutlineEntry> getExtensionEntries() {
		final List<IOutlineEntry> extensionEntries = new ArrayList<>();
		for (final IConfigurationElement extension : Platform.getExtensionRegistry().getConfigurationElementsFor(ENTRY_EXTENSION_ID)) {
			try {
				final Object o = extension.createExecutableExtension("class");
				if (o instanceof IOutlineEntry) {
					final IOutlineEntry entry = (IOutlineEntry) o;
					entry.setConfig(config);
					if (entry.supportsType(null)) {
						extensionEntries.add(entry);
					}
				}
			} catch (final CoreException e) {
				Logger.logError(e);
			}
		}
		return extensionEntries;
	}

}
