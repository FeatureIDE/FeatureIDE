/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.examples.utils;

import java.io.File;
import java.io.FilenameFilter;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.ui.wizards.datatransfer.FileSystemStructureProvider;
import org.eclipse.ui.wizards.datatransfer.IImportStructureProvider;

/**
 * Provides the folder and files for our examples. Contrary to the
 * <code>FileSystemStructureProvider</code>, no SVN meta information are
 * provided.
 * 
 * @author Thomas Thuem
 */
public class ExampleStructureProvider implements IImportStructureProvider {

	/**
	 * Holds a singleton instance of this class.
	 */
	public final static ExampleStructureProvider INSTANCE = new ExampleStructureProvider();

	/**
	 * Holds a singleton instance of the wrapped class.
	 */
	private final static FileSystemStructureProvider SUPER = FileSystemStructureProvider.INSTANCE;

	/**
	 * The filter to not return SVN meta files.
	 */
	private final static FilenameFilter filter = new FilenameFilter() {
		public boolean accept(File dir, String name) {
			return !name.equals(".svn");
		}
	};

	/**
	 * Creates an instance of <code>FileSystemStructureProvider</code>.
	 */
	private ExampleStructureProvider() {
		super();
	}

	/*
	 * (non-Javadoc) Method declared on IImportStructureProvider
	 */
	public List<File> getChildren(Object element) {
		File folder = (File) element;
		String[] children = folder.list(filter);
		int childrenLength = children == null ? 0 : children.length;
		List<File> result = new ArrayList<File>(childrenLength);

		for (int i = 0; i < childrenLength; i++) {
			result.add(new File(folder, children[i]));
		}

		return result;
	}

	/*
	 * (non-Javadoc) Method declared on IImportStructureProvider
	 */
	public InputStream getContents(Object element) {
		return SUPER.getContents(element);
	}

	/*
	 * (non-Javadoc) Method declared on IImportStructureProvider
	 */
	public String getFullPath(Object element) {
		return SUPER.getFullPath(element);
	}

	/*
	 * (non-Javadoc) Method declared on IImportStructureProvider
	 */
	public String getLabel(Object element) {
		return SUPER.getLabel(element);
	}

	/*
	 * (non-Javadoc) Method declared on IImportStructureProvider
	 */
	public boolean isFolder(Object element) {
		return SUPER.isFolder(element);
	}
}
