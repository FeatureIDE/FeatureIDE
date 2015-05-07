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
package de.ovgu.featureide.fm.core.configuration;

import java.io.BufferedReader;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.fm.core.RenamingsManager;

/**
 * Extended configuration format for FeatureIDE projects.</br> Lists all
 * features and indicates the manual and automatic selection.
 * 
 * @author Sebastian Krieter
 */
public class FeatureIDEFormat extends ConfigurationFormat {
	public static final String EXTENSION = "fideconf";

	public List<ConfigurationReader.Warning> read(BufferedReader reader, Configuration configuration) throws IOException {
		final RenamingsManager renamingsManager = configuration.getFeatureModel().getRenamingsManager();
		final List<ConfigurationReader.Warning> warnings = new LinkedList<>();

		final boolean orgPropagate = configuration.isPropagate();
		configuration.setPropagate(false);
		configuration.resetValues();

		String line = null;
		int lineNumber = 1;
		try {
			while ((line = reader.readLine()) != null) {
				if (line.startsWith("#")) {
					continue;
				}
				line = line.trim();
				if (!line.isEmpty()) {
					Selection manual = Selection.UNDEFINED, automatic = Selection.UNDEFINED;
					try {
						switch (Integer.parseInt(line.substring(0, 1))) {
						case 0:
							manual = Selection.UNSELECTED;
							break;
						case 1:
							manual = Selection.SELECTED;
							break;
						case 2:
							break;
						default:
							warnings.add(new ConfigurationReader.Warning("Wrong configuration format", lineNumber));
							break;
						}
						switch (Integer.parseInt(line.substring(1, 2))) {
						case 0:
							automatic = Selection.UNSELECTED;
							break;
						case 1:
							automatic = Selection.SELECTED;
							break;
						case 2:
							break;
						default:
							warnings.add(new ConfigurationReader.Warning("Wrong configuration format", lineNumber));
							break;
						}
					} catch (NumberFormatException e) {
						warnings.add(new ConfigurationReader.Warning("Wrong configuration format", lineNumber));
					}

					final String name = renamingsManager.getNewName(line.substring(2));

					final SelectableFeature feature = configuration.getSelectablefeature(name);
					if (feature == null) {
						warnings.add(new ConfigurationReader.Warning("Feature " + name + " does not exist", lineNumber));
					} else {
						try {
							configuration.setManual(feature, manual);
							configuration.setAutomatic(feature, automatic);
						} catch (SelectionNotPossibleException e) {
							warnings.add(new ConfigurationReader.Warning("Selection not possible on feature " + name, lineNumber));
						}
					}
				}
				lineNumber++;
			}
		} finally {
			configuration.setPropagate(orgPropagate);
		}
		return warnings;
	}

	@Override
	public String write(Configuration configuration) {
		final StringBuilder buffer = new StringBuilder();
		buffer.append("# Lists all features from the model with manual (first digit) and automatic (second digit) selection");
		buffer.append(NEWLINE);
		buffer.append("# 0 = deselected, 1 = selected, 2 = undefined");
		buffer.append(NEWLINE);

		for (SelectableFeature feature : configuration.getFeatures()) {
			buffer.append(Integer.toString(getSelectionCode(feature.getManual())));
			// buffer.append(',');
			buffer.append(Integer.toString(getSelectionCode(feature.getAutomatic())));
			// buffer.append(',');
			buffer.append(feature.getName());
			buffer.append(NEWLINE);
		}

		return buffer.toString();
	}

	private int getSelectionCode(Selection selection) {
		switch (selection) {
		case SELECTED:
			return 1;
		case UNDEFINED:
			return 2;
		case UNSELECTED:
			return 0;
		default:
			return 3;
		}
	}

}
