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
package de.ovgu.featureide.ui.visualization;

import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Platform;
import org.osgi.framework.Bundle;

/**
 * Utils for visualizations
 *
 * @author Jabier Martinez
 */
public class Utils {

	public static File getFileFromPlugin(String pluginId, String relativePath) {
		final Bundle bundle = Platform.getBundle(pluginId);
		final URL fileURL = bundle.getEntry(relativePath);
		File file = null;
		try {
			file = new File(FileLocator.resolve(fileURL).toURI());
		} catch (final URISyntaxException e1) {
			e1.printStackTrace();
		} catch (final IOException e1) {
			e1.printStackTrace();
		}
		return file;
	}

	public static List<String> getLinesOfFile(File file) {
		final List<String> lines = new ArrayList<String>();
		try {
			final FileInputStream fstream = new FileInputStream(file);
			final DataInputStream in = new DataInputStream(fstream);
			final BufferedReader br = new BufferedReader(new InputStreamReader(in));
			String strLine;
			while ((strLine = br.readLine()) != null) {
				lines.add(strLine);
			}
			in.close();
		} catch (final Exception e) {
			e.printStackTrace();
		}
		return lines;
	}

	public static String getStringOfFile(File file) {
		final StringBuilder string = new StringBuilder();
		for (final String line : getLinesOfFile(file)) {
			string.append(line + "\n");
		}
		string.setLength(string.length() - 1);
		return string.toString();
	}

}
