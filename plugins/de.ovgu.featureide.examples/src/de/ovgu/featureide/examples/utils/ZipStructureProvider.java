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

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.ui.wizards.datatransfer.IImportStructureProvider;

import de.ovgu.featureide.examples.ExamplePlugin;

/**
 * This class provides information regarding the context structure and content
 * of specified zip file entry objects.
 * 
 * @author Christian Becker
 */
public class ZipStructureProvider implements IImportStructureProvider  {
	private ZipFile zipFile;

	private ZipEntry root = new ZipEntry("/");//$NON-NLS-1$

	private Map<ZipEntry, List<ZipEntry>>  children;

	private Map<IPath, ZipEntry> directoryEntryCache = new HashMap<IPath, ZipEntry>();

	private int stripLevel;

	/**
	 * Creates a <code>ZipFileStructureProvider</code>, which will operate on
	 * the passed zip file.
	 * 
	 * @param sourceFile
	 *            The source file to create the ZipLeveledStructureProvider
	 *            around
	 */
	public ZipStructureProvider(ZipFile sourceFile) {
		super();
		zipFile = sourceFile;
		stripLevel = 0;
	}

	/**
	 * Creates a new container zip entry with the specified name, if it has 
	 * not already been created. If the parent of the given element does not
	 * already exist it will be recursively created as well.
	 * @param pathname The path representing the container
	 * @return The element represented by this pathname (it may have already existed)
	 */
	protected ZipEntry createContainer(IPath pathname) {
		ZipEntry existingEntry = (ZipEntry) directoryEntryCache.get(pathname);
		if (existingEntry != null) {
			return existingEntry;
		}

		ZipEntry parent;
		if (pathname.segmentCount() == 1) {
			parent = root;
		} else {
			parent = createContainer(pathname.removeLastSegments(1));
		}
		ZipEntry newEntry = new ZipEntry(pathname.toString());
		directoryEntryCache.put(pathname, newEntry);
		List<ZipEntry> childList = new ArrayList<ZipEntry>();
		children.put(newEntry, childList);

		List<ZipEntry> parentChildList = (List<ZipEntry>)children.get(parent);
		parentChildList.add(newEntry);
		return newEntry;
	}

	/**
	 * Creates a new file zip entry with the specified name.
	 */
	protected void createFile(ZipEntry entry) {
		IPath pathname = new Path(entry.getName());
		ZipEntry parent;
		if (pathname.segmentCount() == 1) {
			parent = root;
		} else {
			parent = (ZipEntry) directoryEntryCache.get(pathname
					.removeLastSegments(1));
		}

		List<ZipEntry>  childList = (List<ZipEntry>) children.get(parent);
		childList.add(entry);
	}

	/*
	 * (non-Javadoc) Method declared on IImportStructureProvider
	 */
	public List<ZipEntry>  getChildren(Object element) {
		if (children == null) {
			initialize();
		}

		return ((List<ZipEntry>) children.get(element));
	}

	/*
	 * (non-Javadoc) Method declared on IImportStructureProvider
	 */
	public InputStream getContents(Object element) {
		try {
			return zipFile.getInputStream((ZipEntry) element);
		} catch (IOException e) {
			ExamplePlugin.getDefault().logError(e);
			return null;
		}
	}

	/*
	 * Strip the leading directories from the path
	 */
	private String stripPath(String path) {
		String pathOrig = path;
		for (int i = 0; i < stripLevel; i++) {
			int firstSep = path.indexOf('/');
			// If the first character was a seperator we must strip to the next
			// seperator as well
			if (firstSep == 0) {
				path = path.substring(1);
				firstSep = path.indexOf('/');
			}
			// No seperator wasw present so we're in a higher directory right
			// now
			if (firstSep == -1) {
				return pathOrig;
			}
			path = path.substring(firstSep);
		}
		return path;
	}

	/*
	 * (non-Javadoc) Method declared on IImportStructureProvider
	 */
	public String getFullPath(Object element) {
		return stripPath(((ZipEntry) element).getName());
	}

	/*
	 * (non-Javadoc) Method declared on IImportStructureProvider
	 */
	public String getLabel(Object element) {
		if (element.equals(root)) {
			return ((ZipEntry) element).getName();
		}

		return stripPath(new Path(((ZipEntry) element).getName()).lastSegment());
	}

	/**
	 * Returns the entry that this importer uses as the root sentinel.
	 * 
	 * @return java.util.zip.ZipEntry
	 */
	public Object getRoot() {
		return root;
	}

	/**
	 * Returns the zip file that this provider provides structure for.
	 * 
	 * @return The zip file
	 */
	public ZipFile getZipFile() {
		return zipFile;
	}


	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.internal.wizards.datatransfer.ILeveledImportStructureProvider#closeArchive()
	 */
	public boolean closeArchive(){
		try {
			getZipFile().close();
		} catch (IOException e) {
			ExamplePlugin.getDefault().logError("Could not Close Archieve: ",e);
			return false;
		}
		return true;
	}
	
	/**
	 * Initializes this object's children table based on the contents of the
	 * specified source file.
	 */
	protected void initialize() {
		children = new HashMap<ZipEntry, List<ZipEntry>>(1000);

		children.put(root, new ArrayList<ZipEntry>());
		Enumeration<?> entries = zipFile.entries();
		while (entries.hasMoreElements()) {
			ZipEntry entry = (ZipEntry) entries.nextElement();
			IPath path = new Path(entry.getName()).addTrailingSeparator();

			if (entry.isDirectory()) {
				createContainer(path);
			} else
			{
				// Ensure the container structure for all levels above this is initialized
				// Once we hit a higher-level container that's already added we need go no further
				int pathSegmentCount = path.segmentCount();
				if (pathSegmentCount > 1) {
					createContainer(path.uptoSegment(pathSegmentCount - 1));
				}
				createFile(entry);
			}
		}
	}

	/*
	 * (non-Javadoc) Method declared on IImportStructureProvider
	 */
	public boolean isFolder(Object element) {
		return ((ZipEntry) element).isDirectory();
	}

	public void setStrip(int level) {
		stripLevel = level;
	}

	public int getStrip() {
		return stripLevel;
	}
}
