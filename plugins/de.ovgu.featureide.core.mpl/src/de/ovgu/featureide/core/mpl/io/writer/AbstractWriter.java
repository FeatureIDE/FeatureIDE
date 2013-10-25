/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.core.mpl.io.writer;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.nio.charset.Charset;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.mpl.InterfaceProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;

/**
 * Writes data to a file.
 * 
 * @author Sebastian Krieter
 */
public abstract class AbstractWriter {
	protected static final String
		LINE_SEPARATOR = System.getProperty("line.separator");
	
	protected final InterfaceProject interfaceProject;
	
	public AbstractWriter(InterfaceProject interfaceProject) {
		this.interfaceProject = interfaceProject;
	}
	
	public static void clearFolder(IFolder folder) {
		try {
			if (folder.exists()) {
				folder.delete(true, null);
			}
			folder.create(false, true, null);
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
		}
	}

	public static void writeToFile(IFile file, String content) {
		InputStream inputStream = new ByteArrayInputStream(
				content.getBytes(Charset.availableCharsets().get("UTF-8")));

		try {
			synchronized (file) {
				if (file.isAccessible()) {
					file.setContents(inputStream, false, true, null);
				} else {
					file.create(inputStream, true, null);
				}
			}
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
		}
	}
	
	protected void appendToFile(IFile file, String newContent) {
		InputStream inputStream = new ByteArrayInputStream(
				newContent.getBytes(Charset.availableCharsets().get("UTF-8")));

		try {
			synchronized (file) {
				if (file.isAccessible()) {
					file.appendContents(inputStream, false, true, null);
				} else {
					file.create(inputStream, true, null);
				}
			}
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
		}
	}
}
