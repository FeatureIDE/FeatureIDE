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
package de.ovgu.featureide.examples.utils;

import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.Collections;
import java.util.List;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.ui.wizards.datatransfer.IImportStructureProvider;
import org.eclipse.ui.wizards.datatransfer.ImportOperation;

import de.ovgu.featureide.examples.ExamplePlugin;

/**
 * Simple StructureProvider used by the class {@link ImportOperation}
 *
 * @author Reimar Schroeter
 */
public class SimpleStructureProvider implements IImportStructureProvider {

	private final String project;

	public SimpleStructureProvider(String project) {
		super();
		this.project = project;
	}

	@Override
	public List<?> getChildren(Object element) {
		return Collections.EMPTY_LIST;
	}

	@Override
	public InputStream getContents(Object element) {
		final IPath p = new Path((String) element);
		try {
			return new URL("platform:/plugin/de.ovgu.featureide.examples/featureide_examples/" + project + "/" + p.toString()).openConnection()
					.getInputStream();
		} catch (final IOException e) {
			ExamplePlugin.getDefault().logError(e);
		}
		return null;
	}

	@Override
	public String getFullPath(Object element) {
		return (String) element;
	}

	@Override
	public String getLabel(Object element) {
		final IPath path = new Path((String) element);
		return path.lastSegment();
	}

	@Override
	public boolean isFolder(Object element) {
		return false;
	}

}
