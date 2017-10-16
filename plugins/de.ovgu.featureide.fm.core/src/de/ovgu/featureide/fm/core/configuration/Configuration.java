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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.Set;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;

/**
 * Represents a configuration and provides operations for the configuration process.
 */
public class Configuration implements Cloneable {

	ArrayList<SelectableFeature> features = new ArrayList<>();
	Hashtable<String, SelectableFeature> table = new Hashtable<>();

	private IFeatureModel featureModel;
	private SelectableFeature root;

	/**
	 * This method creates a clone of the given {@link Configuration}
	 *
	 * @param configuration The configuration to clone
	 */
	protected Configuration(Configuration configuration) {
		featureModel = configuration.featureModel;
		root = initRoot();

		for (final SelectableFeature f : configuration.features) {
			setManual(f.getName(), f.getManual());
			setAutomatic(f.getName(), f.getAutomatic());
		}
	}

	/**
	 * Copy constructor. Copies the status of a given configuration.
	 *
	 * @param configuration the old configuration.
	 * @param featureModel the underlying feature model. The model can be different from the model of the old configuration.
	 */
	// public Configuration(Configuration configuration, IFeatureModel featureModel) {
	// this.featureModel = featureModel;
	// this.root = initRoot();
	//
	// for (SelectableFeature oldFeature : configuration.features) {
	// final SelectableFeature newFeature = table.get(oldFeature.getName());
	// if (newFeature != null) {
	// newFeature.setManual(oldFeature.getManual());
	// }
	// }
	// }

	public Configuration(IFeatureModel featureModel) {
		this.featureModel = featureModel;
		root = initRoot();
	}

	public void setFeatureModel(IFeatureModel featureModel) {
		final ArrayList<SelectableFeature> oldFeatures = features;
		features = new ArrayList<>(oldFeatures.size());
		table.clear();

		this.featureModel = featureModel;
		root = initRoot();

		for (final SelectableFeature oldFeature : oldFeatures) {
			final SelectableFeature newFeature = table.get(oldFeature.getName());
			if (newFeature != null) {
				newFeature.setManual(oldFeature.getManual());
				newFeature.setAutomatic(oldFeature.getAutomatic());
			}
		}
	}

	private void initFeatures(SelectableFeature sFeature, IFeature feature) {
		if ((sFeature != null) && (sFeature.getName() != null)) {
			features.add(sFeature);
			table.put(sFeature.getName(), sFeature);

			for (final IFeatureStructure child : feature.getStructure().getChildren()) {
				final SelectableFeature sChild = new SelectableFeature(child.getFeature());
				sFeature.addChild(sChild);
				initFeatures(sChild, child.getFeature());
			}
		}
	}

	private SelectableFeature initRoot() {
		final IFeature featureRoot = FeatureUtils.getRoot(featureModel);
		final SelectableFeature root = new SelectableFeature(featureRoot);

		if (featureRoot != null) {
			initFeatures(root, featureRoot);
		} else {
			features.add(root);
			table.put(root.getName(), root);
		}

		return root;
	}

	void resetAutomaticValues() {
		for (final SelectableFeature feature : features) {
			feature.setAutomatic(Selection.UNDEFINED);
		}
	}

	public void setAutomatic(SelectableFeature feature, Selection selection) {
		feature.setAutomatic(selection);
	}

	public void setAutomatic(String name, Selection selection) {
		final SelectableFeature feature = table.get(name);
		if (feature == null) {
			throw new FeatureNotFoundException();
		}
		setAutomatic(feature, selection);
	}

	public IFeatureModel getFeatureModel() {
		return featureModel;
	}

	public List<SelectableFeature> getFeatures() {
		return Collections.unmodifiableList(features);
	}

	public List<SelectableFeature> getManualFeatures() {
		final List<SelectableFeature> featureList = new ArrayList<>();
		for (final SelectableFeature selectableFeature : features) {
			if ((selectableFeature.getAutomatic() == Selection.UNDEFINED) && !selectableFeature.getFeature().getStructure().hasHiddenParent()) {
				featureList.add(selectableFeature);
			}
		}
		return featureList;
	}

	public SelectableFeature getRoot() {
		return root;
	}

	public SelectableFeature getSelectableFeature(String name) {
		return table.get(name);
	}

	public Set<String> getSelectedFeatureNames() {
		final Set<String> result = new HashSet<>();
		for (final SelectableFeature feature : features) {
			if (feature.getSelection() == Selection.SELECTED) {
				result.add(feature.getName());
			}
		}
		return result;
	}

	public List<IFeature> getSelectedFeatures() {
		return getFeatures(Selection.SELECTED);
	}

	public List<IFeature> getUnSelectedFeatures() {
		return getFeatures(Selection.UNSELECTED);
	}

	public List<IFeature> getUndefinedSelectedFeatures() {
		return getFeatures(Selection.UNDEFINED);
	}

	private List<IFeature> getFeatures(final Selection selection) {
		final List<IFeature> result = new ArrayList<>();
		for (final SelectableFeature feature : features) {
			if (feature.getSelection() == selection) {
				result.add(feature.getFeature());
			}
		}
		return result;
	}

	/**
	 * Turns all automatic into manual values
	 *
	 * @param discardDeselected if {@code true} all automatic deselected features get undefined instead of manual deselected
	 */
	public void makeManual(boolean discardDeselected) {
		for (final SelectableFeature feature : features) {
			final Selection autoSelection = feature.getAutomatic();
			if (autoSelection != Selection.UNDEFINED) {
				feature.setAutomatic(Selection.UNDEFINED);
				if (!discardDeselected || (autoSelection == Selection.SELECTED)) {
					feature.setManual(autoSelection);
				}
			}
		}
	}

	public void resetValues() {
		for (final SelectableFeature feature : features) {
			feature.setManual(Selection.UNDEFINED);
			feature.setAutomatic(Selection.UNDEFINED);
		}
	}

	public void setManual(SelectableFeature feature, Selection selection) {
		feature.setManual(selection);
	}

	public void setManual(String name, Selection selection) {
		final SelectableFeature feature = table.get(name);
		if (feature == null) {
			throw new FeatureNotFoundException();
		}
		setManual(feature, selection);
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		for (final SelectableFeature feature : features) {
			if ((feature.getSelection() == Selection.SELECTED) && feature.getFeature().getStructure().isConcrete()) {
				builder.append(feature.getFeature().getName());
				builder.append("\n");
			}
		}
		return builder.toString();
	}

	@Override
	public Configuration clone() {
		if (!this.getClass().equals(Configuration.class)) {
			try {
				return (Configuration) super.clone();
			} catch (final CloneNotSupportedException e) {
				Logger.logError(e);
				throw new RuntimeException("Cloning is not supported for " + this.getClass());
			}
		}
		return new Configuration(this);
	}

}
