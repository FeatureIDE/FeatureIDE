/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import static de.ovgu.featureide.fm.core.localization.StringTable.CANNOT_BE_SELECTED;
import static de.ovgu.featureide.fm.core.localization.StringTable.DOES_NOT_EXIST;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURE;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.IS_CORRUPT__NO_ENDING_QUOTATION_MARKS_FOUND_;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.List;
import java.util.StringTokenizer;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.RenamingsManager;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.APersistentFormat;
import de.ovgu.featureide.fm.core.io.IConfigurationFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.localization.StringTable;

/**
 * Simple configuration format.<br> Lists all selected features in the user-defined order (if specified).
 *
 * @author Sebastian Krieter
 */
public class DefaultFormat extends APersistentFormat<Configuration> implements IConfigurationFormat {

	public static final String ID = PluginID.PLUGIN_ID + ".format.config." + DefaultFormat.class.getSimpleName();

	private static final String NEWLINE = System.lineSeparator();

	@Override
	public ProblemList read(Configuration configuration, CharSequence source) {
		final IFeatureModel featureModel = configuration.getFeatureModel();
		final RenamingsManager renamingsManager = featureModel == null ? null : featureModel.getRenamingsManager();
		final ProblemList warnings = new ProblemList();

		String line = null;
		int lineNumber = 1;
		try (BufferedReader reader = new BufferedReader(new StringReader(source.toString()))) {
			while ((line = reader.readLine()) != null) {
				if (line.startsWith("#") || line.isEmpty() || line.equals(" ")) {
					continue;
				}
				// the string tokenizer is used to also support the expression
				// format used by FeatureHouse
				final StringTokenizer tokenizer = new StringTokenizer(line);
				final List<String> hiddenFeatures = new ArrayList<>();
				while (tokenizer.hasMoreTokens()) {
					String name = tokenizer.nextToken(" ");
					if (name.startsWith("\"")) {
						try {
							name = name.substring(1);
							name += tokenizer.nextToken("\"");
							if (!tokenizer.nextToken(" ").startsWith("\"")) {
								warnings.add(new Problem(FEATURE_ + name + IS_CORRUPT__NO_ENDING_QUOTATION_MARKS_FOUND_, lineNumber));
							}
						} catch (final RuntimeException e) {
							warnings.add(new Problem(FEATURE_ + name + IS_CORRUPT__NO_ENDING_QUOTATION_MARKS_FOUND_, lineNumber));
						}
					}
					name = renamingsManager == null ? name : renamingsManager.getNewName(name);
					final IFeature feature = featureModel != null ? featureModel.getFeature(name) : null;
					if ((feature != null) && feature.getStructure().hasHiddenParent()) {
						hiddenFeatures.add(name);
					} else {
						try {
							configuration.setManual(name, Selection.SELECTED);
						} catch (final FeatureNotFoundException e) {
							warnings.add(new Problem(FEATURE + name + DOES_NOT_EXIST, lineNumber));
						} catch (final SelectionNotPossibleException e) {
							warnings.add(new Problem(FEATURE + name + CANNOT_BE_SELECTED, lineNumber));
						}
					}
				}
				for (final String name : hiddenFeatures) {
					try {
						configuration.setAutomatic(name, Selection.SELECTED);
					} catch (final FeatureNotFoundException e) {
						warnings.add(new Problem(FEATURE + name + DOES_NOT_EXIST, lineNumber));
					} catch (final SelectionNotPossibleException e) {
						warnings.add(new Problem(FEATURE + name + CANNOT_BE_SELECTED, lineNumber));
					}
				}
				lineNumber++;
			}
		} catch (final IOException e) {
			warnings.clear();
			warnings.add(new Problem(e));
			return warnings;
		}
		return warnings;
	}

	public String readLine(String line) {
		return null;
	}

	@Override
	public String write(Configuration configuration) {
		final StringBuilder buffer = new StringBuilder();
		final IFeatureModel featureModel = configuration.getFeatureModel();
		if ((featureModel != null) && featureModel.isFeatureOrderUserDefined()) {
			writeFeatureOrder(configuration, buffer, featureModel);
		} else if (configuration.getRoot() != null) {
			writeFeatureTree(configuration.getRoot(), buffer, featureModel);
		} else {
			writeFeatureList(configuration, buffer, featureModel);
		}
		return buffer.toString();
	}

	private void writeFeatureOrder(Configuration configuration, final StringBuilder buffer, final IFeatureModel featureModel) {
		final List<String> list = featureModel.getFeatureOrderList();
		for (final String name : list) {
			final SelectableFeature selectableFeature = configuration.getSelectableFeature(name, false);
			if (selectableFeature != null) {
				writeSelectedFeature(buffer, selectableFeature, featureModel);
			}
		}
	}

	private void writeFeatureList(Configuration configuration, final StringBuilder buffer, IFeatureModel featureModel) {
		for (final SelectableFeature feature : configuration.getFeatures()) {
			writeSelectedFeature(buffer, feature, featureModel);
		}
	}

	private void writeFeatureTree(SelectableFeature feature, StringBuilder buffer, IFeatureModel featureModel) {
		writeSelectedFeature(buffer, feature, featureModel);
		for (final TreeElement child : feature.getChildren()) {
			writeFeatureTree((SelectableFeature) child, buffer, featureModel);
		}
	}

	private void writeSelectedFeature(final StringBuilder buffer, final SelectableFeature feature, IFeatureModel featureModel) {
		if (((featureModel == null) || feature.getFeature().getStructure().isConcrete()) && (feature.getSelection() == Selection.SELECTED)) {
			if (feature.getName().contains(" ")) {
				buffer.append("\"" + feature.getName() + "\"" + NEWLINE);
			} else {
				buffer.append(feature.getName() + NEWLINE);
			}
		}
	}

	@Override
	public String getSuffix() {
		return StringTable.CONFIG;
	}

	@Override
	public DefaultFormat getInstance() {
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
		return "FeatureList";
	}

}
