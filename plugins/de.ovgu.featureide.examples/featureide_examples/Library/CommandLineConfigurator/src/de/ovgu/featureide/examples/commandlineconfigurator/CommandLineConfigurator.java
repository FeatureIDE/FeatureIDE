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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.examples.commandlineconfigurator;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationAnalyzer;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.init.FMCoreLibrary;
import de.ovgu.featureide.fm.core.init.LibraryManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;

/**
 * A simple configurator without GUI using the FeatureIDE library.
 *
 * @author Thomas Thuem
 * @author Sebastian Krieter
 */
public class CommandLineConfigurator {

	static {
		LibraryManager.registerLibrary(FMCoreLibrary.getInstance());
	}

	private static FeatureModelFormula featureModel;
	private static Configuration configuration;
	private static ConfigurationAnalyzer configurationAnalyzer;

	private static ArrayList<Object> undefinedFeatures = new ArrayList<Object>();
	private static ArrayList<Object> manuallySelectedFeatures = new ArrayList<Object>();
	private static ArrayList<Object> automaticallySelectedFeatures = new ArrayList<Object>();
	private static ArrayList<Object> automaticallyDeselectedFeatures = new ArrayList<Object>();

	public static void main(String[] args) {
		final Path path = Paths.get("model.xml");
		try {
			createEmptyConfiguration(path);
			updateLists();

			BufferedReader br = new BufferedReader(new InputStreamReader(System.in));

			while (true) {
				System.out.println("Manually selected:        " + manuallySelectedFeatures);
				System.out.println("Automatically selected:   " + automaticallySelectedFeatures);
				System.out.println("Automatically deselected: " + automaticallyDeselectedFeatures);
				System.out.println("Selection undefined:      " + undefinedFeatures);
				System.out.println();

				System.out.print("Select feature X with +X or revert selection with -X: ");
				String s = br.readLine();
				System.out.println();

				String operation = s.substring(0, 1);
				String feature = s.substring(1, s.length());

				if (operation.equals("+")) {
					modifyConfiguration(feature, Selection.SELECTED);
				} else {
					modifyConfiguration(feature, Selection.UNDEFINED);
				}
			}
		} catch (IOException e) {
			System.err.println(e.getMessage());
		}
	}

	private static void createEmptyConfiguration(final Path path) throws IOException {
		final FileHandler<IFeatureModel> fh = FeatureModelManager.getFileHandler(path);
		if (!fh.getLastProblems().containsError()) {
			featureModel = new FeatureModelFormula(fh.getObject());
			configuration = new Configuration(featureModel);
			configurationAnalyzer = new ConfigurationAnalyzer(featureModel, configuration);
		} else {
			throw new IOException("Feature model could not be loaded");
		}
	}

	private static void updateLists() {
		undefinedFeatures.clear();
		manuallySelectedFeatures.clear();
		automaticallyDeselectedFeatures.clear();
		automaticallySelectedFeatures.clear();
		
		configurationAnalyzer.update(true, null);
		final List<SelectableFeature> features = getSelectableFeatures();

		for (SelectableFeature feature : features) {
			switch (feature.getSelection()) {
			case SELECTED:
				if (feature.getAutomatic() != Selection.UNDEFINED) {
					automaticallySelectedFeatures.add(feature);
				} else {
					manuallySelectedFeatures.add(feature);
				}
				break;
			case UNDEFINED:
				undefinedFeatures.add(feature);
				break;
			case UNSELECTED:
				if (feature.getAutomatic() != Selection.UNDEFINED) {
					automaticallyDeselectedFeatures.add(feature);
				}
				break;
			default:
				break;
			}
		}
	}

	private static List<SelectableFeature> getSelectableFeatures() {
		final List<SelectableFeature> features = Functional.toList(Functional.filter(configuration.getFeatures(),
				feature -> feature.getFeature().getStructure().isConcrete()
						&& !feature.getFeature().getStructure().hasHiddenParent()));
		Collections.sort(features, (SelectableFeature o1, SelectableFeature o2) -> {
			if (o1.getAutomatic() == Selection.UNDEFINED) {
				if (o2.getAutomatic() == Selection.UNDEFINED) {
					return o1.getName().compareTo(o2.getName());
				} else {
					return -1;
				}
			} else {
				if (o2.getAutomatic() == Selection.UNDEFINED) {
					return 1;
				} else {
					return o1.getName().compareTo(o2.getName());
				}
			}
		});
		return features;
	}

	private static void modifyConfiguration(String feature, final Selection selection) {
		for (SelectableFeature selectableFeature : configuration.getFeatures()) {
			if (selectableFeature.getName().equals(feature)) {
				modifyConfiguration(selectableFeature, selection);
			}
		}
	}

	private static void modifyConfiguration(SelectableFeature selectedValue, final Selection selection) {
		if (selectedValue instanceof SelectableFeature) {
			try {
				configuration.setManual(selectedValue, selection);
			} catch (Exception e) {
				System.err.println(e.getMessage());
				System.err.println();
				System.err.flush();
				return;
			}
			updateLists();
		}
	}

}
