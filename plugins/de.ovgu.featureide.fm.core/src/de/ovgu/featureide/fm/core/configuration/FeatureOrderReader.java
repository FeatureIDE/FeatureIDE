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
package de.ovgu.featureide.fm.core.configuration;

import static de.ovgu.featureide.fm.core.localization.StringTable.CAN_NOT_READ__ORDER_FILE;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.LinkedList;
import java.util.Scanner;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.io.FeatureOrderFormat;

/**
 * Read the .order file from the project directory. The constructor need the location of the project as parameter
 *
 * @deprecated Use {@link FeatureOrderFormat} instead.
 *
 * @author Christian Becker
 */
@Deprecated
public class FeatureOrderReader {

	private final File file;

	public FeatureOrderReader(File file) {
		this.file = new File(file.toString() + System.getProperty("file.separator") + ".order");
	}

	/**
	 *
	 * @return Return the feature order
	 */

	public LinkedList<String> featureOrderRead() {
		final LinkedList<String> list = new LinkedList<String>();
		try {
			final Scanner scanner = new Scanner(file, "UTF-8");
			while (scanner.hasNext()) {
				list.add(scanner.next());
			}
			scanner.close();
		} catch (final FileNotFoundException e) {
			Logger.logInfo(CAN_NOT_READ__ORDER_FILE);
		}

		return list;
	}

}
