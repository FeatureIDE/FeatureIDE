/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.nio.charset.Charset;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.prop4j.Literal;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.FMCorePlugin;

/**
 * Several constants for I/O-operations.
 * 
 * @author Sebastian Krieter
 */
public final class IOConstants {
	public static final String
		FILENAME_MODEL = "model.xml",
		FILENAME_CONFIG = "configuration.config",
		FILENAME_EXTCONFIG = ".xconf",
		FILENAME_EXPORTFST = "fst_exported_file.txt",
		FILENAME_COMPARE_MATRIX = "similarity_matrix.csv",
		
		FOLDERNAME_FEATURE_ROLES = "features",
		FOLDERNAME_FEATURE_INTERFACES = "feature_interfaces",
		FOLDERNAME_WRAPPER_INTERFACES = "wrapper_interfaces",
		
		EXTENSION_JAVA = ".java",
		EXTENSION_JAK = ".jak",
		EXTENSION_SOLUTION = ".solution",
	
		LINE_SEPARATOR = System.getProperty("line.separator", "\n");
	
	public static Node[] buildNodeForFeature(String featureName) {
		return new Node[] {new Literal(featureName, true)};		
	}
	
	public static void clearFolder(IFolder folder) {
		try {
			if (folder.exists()) {
				folder.delete(true, null);
			}
			folder.create(false, true, null);
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	public static void writeToFile(IFile file, String content) {
		InputStream inputStream = new ByteArrayInputStream(
				content.getBytes(Charset.defaultCharset())); //Charset.availableCharsets().get("UTF-8")));

		try {
			synchronized (file) {
				if (file.isAccessible()) {
					file.setContents(inputStream, false, true, null);
				} else {
					file.create(inputStream, true, null);
				}
			}
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}
	
	public static void appendToFile(IFile file, String newContent) {
		InputStream inputStream = new ByteArrayInputStream(
				newContent.getBytes(Charset.defaultCharset())); //Charset.availableCharsets().get("UTF-8")));

		try {
			synchronized (file) {
				if (file.isAccessible()) {
					file.appendContents(inputStream, false, true, null);
				} else {
					file.create(inputStream, true, null);
				}
			}
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}
}
