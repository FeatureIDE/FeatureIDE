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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.configuration;

import static de.ovgu.featureide.fm.core.localization.StringTable.DOES_NOT_EXIST;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURE;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECTION_NOT_POSSIBLE_ON_FEATURE;
import static de.ovgu.featureide.fm.core.localization.StringTable.WRONG_CONFIGURATION_FORMAT;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.RenamingsManager;
import de.ovgu.featureide.fm.core.io.APersistentFormat;
import de.ovgu.featureide.fm.core.io.IConfigurationFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.localization.StringTable;

/**
 * Extended configuration format for FeatureIDE projects.</br> Lists all features and indicates the manual and automatic selection.
 *
 * @author Sebastian Krieter
 */
public class FeatureIDEFormat extends APersistentFormat<Configuration> implements IConfigurationFormat {

	public static final String ID = PluginID.PLUGIN_ID + ".format.config." + FeatureIDEFormat.class.getSimpleName();

	public static final String EXTENSION = StringTable.FIDECONF;

	private static final String NEWLINE = System.lineSeparator();

	@Override
	public ProblemList read(Configuration configuration, CharSequence source) {
		final RenamingsManager renamingsManager = configuration.getFeatureModel().getRenamingsManager();
		final ProblemList warnings = new ProblemList();

		final boolean orgPropagate = configuration.isPropagate();
		configuration.setPropagate(false);
		configuration.resetValues();

		String line = null;
		int lineNumber = 1;
		try (BufferedReader reader = new BufferedReader(new StringReader(source.toString()))) {
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
							warnings.add(new Problem(WRONG_CONFIGURATION_FORMAT, lineNumber));
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
							warnings.add(new Problem(WRONG_CONFIGURATION_FORMAT, lineNumber));
							break;
						}
					} catch (final NumberFormatException e) {
						warnings.add(new Problem(WRONG_CONFIGURATION_FORMAT, lineNumber, e));
					}

					final String name = renamingsManager.getNewName(line.substring(2));

					final SelectableFeature feature = configuration.getSelectablefeature(name);
					if (feature == null) {
						warnings.add(new Problem(FEATURE + name + DOES_NOT_EXIST, lineNumber));
					} else {
						try {
							configuration.setManual(feature, manual);
							configuration.setAutomatic(feature, automatic);
						} catch (final SelectionNotPossibleException e) {
							warnings.add(new Problem(SELECTION_NOT_POSSIBLE_ON_FEATURE + name, lineNumber, e));
						}
					}
				}
				lineNumber++;
			}
		} catch (final IOException e) {
			warnings.add(new Problem(e));
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

		for (final SelectableFeature feature : configuration.getFeatures()) {
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

	@Override
	public String getSuffix() {
		return EXTENSION;
	}

	@Override
	public FeatureIDEFormat getInstance() {
		return this;
	}

	@Override
	public boolean supportsRead() {
		return true;
	}

	@Override
	public boolean supportsWrite() {
		return true;
	}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public String getName() {
		return "FeatureIDE-Internal";
	}

}
