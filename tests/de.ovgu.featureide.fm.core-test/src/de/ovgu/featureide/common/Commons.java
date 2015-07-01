package de.ovgu.featureide.common;

import java.io.File;
import java.io.FileFilter;
import java.io.FileNotFoundException;
import java.util.List;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;


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

/**
 * @author Marcus Pinnecke
 */
public class Commons {

	
	public static class FileFilterByExtension implements FileFilter {
		
		final String fileExtension;
		
		public FileFilterByExtension(final String fileExtension) {
			assert (fileExtension != null && !fileExtension.isEmpty());
			
			this.fileExtension = fileExtension;
		}
		
		@Override
		public boolean accept(final File pathname) {
			return pathname.getName().endsWith("." + fileExtension);
		}
	};
	
	/**
	 * Returns a file reference to <code>remotePath</code> via a absolute path on TeamCity build server or
	 * the file reference to <code>localClassPath</code> which should be inside the class path. The return
	 * value could be <code>null</code> if no such file exists on both places.
	 * 
	 * @param remotePath Path to desired file on TeamCity
	 * @param localClassPath Path to desired file on class path
	 * @return File instance to that file
	 */
	public static final File getFile(final String remotePath, final String localClassPath) {
		final File folder = new File(remotePath);
		return folder.canRead() ? folder : new File(ClassLoader.getSystemResource(localClassPath).getPath());
	}
	
	public final static FeatureModel loadFeatureModelFromFile(final String featureModelXmlFilename, final String remotePath, final String localClassPath) {
		return loadFeatureModelFromFile(featureModelXmlFilename, new FileFilterByExtension(extractFileExtension(featureModelXmlFilename)), remotePath, localClassPath);
	}
	
	/**
	 * @param featureModelXmlFilename
	 * @return
	 */
	public static String extractFileExtension(String filename) {
		final int position = filename.lastIndexOf('.');
		if (position > 0) {
		    return filename.substring(position+1);
		} else return "";
	}

	public final static FeatureModel loadFeatureModelFromFile(final String featureModelXmlFilename, final FileFilter filter, final String remotePath, final String localClassPath) {
		FeatureModel fm = new FeatureModel();
		File modelFileFolder = getFile(remotePath, localClassPath);
		for (File f : modelFileFolder.listFiles(filter)) {
			if (f.getName().equals(featureModelXmlFilename)) {
				try {
					new XmlFeatureModelReader(fm).readFromFile(f);
					break;
				} catch (FileNotFoundException e) {
					e.printStackTrace();
				} catch (UnsupportedModelException e) {
					e.printStackTrace();
				}
			}
		}
		return fm;
	}

	public final static <T> String join(T delimiter, List<T> list) {
		StringBuilder sb = new StringBuilder();
		if (list != null && !list.isEmpty()) {
			for (int i = 0; i < list.size(); i++) {
				sb.append(list.get(i));
				if (i <= list.size() - 1)
					sb.append(delimiter);
			}
		}
		return sb.toString();
	}
}
