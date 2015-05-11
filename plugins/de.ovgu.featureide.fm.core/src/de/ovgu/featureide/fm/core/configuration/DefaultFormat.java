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
import java.util.Set;
import java.util.StringTokenizer;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.RenamingsManager;

/**
 * Simple configuration format.</br> Lists all selected features in the
 * user-defined order (if specified).
 * 
 * @author Sebastian Krieter
 */
public class DefaultFormat extends ConfigurationFormat {

	public List<ConfigurationReader.Warning> read(BufferedReader reader, Configuration configuration) throws IOException {
		final RenamingsManager renamingsManager = configuration.getFeatureModel().getRenamingsManager();
		final List<ConfigurationReader.Warning> warnings = new LinkedList<>();

		final boolean orgPropagate = configuration.isPropagate();
		configuration.setPropagate(false);
		configuration.resetValues();
		
		String line = null;
		int lineNumber = 1;
		while ((line = reader.readLine()) != null) {
			if (line.startsWith("#") || line.isEmpty() || line.equals(" ")) {
				continue;
			}
			// the string tokenizer is used to also support the expression
			// format used by FeatureHouse
			final StringTokenizer tokenizer = new StringTokenizer(line);
			final LinkedList<String> hiddenFeatures = new LinkedList<>();
			while (tokenizer.hasMoreTokens()) {
				String name = tokenizer.nextToken(" ");
				if (name.startsWith("\"")) {
					try {
						name = name.substring(1);
						name += tokenizer.nextToken("\"");
						if (!tokenizer.nextToken(" ").startsWith("\"")) {
							warnings.add(new ConfigurationReader.Warning("Feature '" + name + "' is corrupt. No ending quotation marks found.", lineNumber));
						}
					} catch (RuntimeException e) {
						warnings.add(new ConfigurationReader.Warning("Feature '" + name + "' is corrupt. No ending quotation marks found.", lineNumber));
					}
				}
				name = renamingsManager.getNewName(name);
				Feature feature = configuration.getFeatureModel().getFeature(name);
				if (feature != null && feature.hasHiddenParent()) {
					hiddenFeatures.add(name);
				} else {
					try {
						configuration.setManual(name, Selection.SELECTED);
					} catch (FeatureNotFoundException e) {
						warnings.add(new ConfigurationReader.Warning("Feature " + name + " does not exist", lineNumber));
					} catch (SelectionNotPossibleException e) {
						warnings.add(new ConfigurationReader.Warning("Feature " + name + " cannot be selected", lineNumber));
					}
				}
			}
			for (String name : hiddenFeatures) {
				try {
					configuration.setAutomatic(name, Selection.SELECTED);
				} catch (FeatureNotFoundException e) {
					warnings.add(new ConfigurationReader.Warning("Feature " + name + " does not exist", lineNumber));
				} catch (SelectionNotPossibleException e) {
					warnings.add(new ConfigurationReader.Warning("Feature " + name + " cannot be selected", lineNumber));
				}
			}
			lineNumber++;
		}
		configuration.setPropagate(orgPropagate);
		configuration.update();
		return warnings;
	}

	public String readLine(String line) {

		return null;
	}

	@Override
	public String write(Configuration configuration) {
		final StringBuilder buffer = new StringBuilder();
		final FeatureModel featureModel = configuration.getFeatureModel();
		if (featureModel.isFeatureOrderUserDefined()) {
			final List<String> list = featureModel.getFeatureOrderList();
			final Set<String> featureSet = configuration.getSelectedFeatureNames();
			for (String s : list) {
				if (featureSet.contains(s)) {
					if (s.contains(" ")) {
						buffer.append("\"" + s + "\"" + NEWLINE);
					} else {
						buffer.append(s + NEWLINE);
					}
				}
			}
			return buffer.toString();
		}

		writeSelectedFeatures(configuration.getRoot(), buffer);
		return buffer.toString();
	}

	private void writeSelectedFeatures(SelectableFeature feature, StringBuilder buffer) {
		if (feature.getFeature().isConcrete() && feature.getSelection() == Selection.SELECTED) {
			if (feature.getName().contains(" ")) {
				buffer.append("\"" + feature.getName() + "\"" + NEWLINE);
			} else {
				buffer.append(feature.getName() + NEWLINE);
			}
		}
		for (TreeElement child : feature.getChildren()) {
			writeSelectedFeatures((SelectableFeature) child, buffer);
		}
	}

}
