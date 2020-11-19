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
package de.ovgu.featureide.fm.core.configuration;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Set;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.Renaming;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.ConfigurationFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.DefaultConfigurationFactory;

/**
 * Represents a configuration and provides operations for the configuration process.
 */
public class Configuration implements Cloneable {

	protected final LinkedHashMap<String, SelectableFeature> selectableFeatures = new LinkedHashMap<>();
	protected FeatureModelFormula featureModel;
	protected SelectableFeature root;

	/**
	 * This method creates a clone of the given {@link Configuration}
	 *
	 * @param configuration The configuration to clone
	 */
	protected Configuration(Configuration configuration) {
		updateFeatures(configuration.featureModel);
		for (final SelectableFeature f : configuration.selectableFeatures.values()) {
			final SelectableFeature newFeature = getSelectableFeature(f.getName(), featureModel == null);
			if (newFeature != null) {
				setManual(newFeature, f.getManual());
				setAutomatic(newFeature, f.getAutomatic());
				newFeature.cloneProperties(f);
			}
		}
	}

	/**
	 * Copy constructor. Copies the status of a given configuration.
	 *
	 * @param configuration the old configuration.
	 * @param featureModel the underlying feature model. The model can be different from the model of the old configuration.
	 */
	public Configuration(Configuration configuration, FeatureModelFormula featureModel) {
		updateFeatures(featureModel);
		for (final SelectableFeature oldFeature : configuration.selectableFeatures.values()) {
			final SelectableFeature newFeature = selectableFeatures.get(oldFeature.getName());
			if (newFeature != null) {
				newFeature.setManual(oldFeature.getManual());
				newFeature.setAutomatic(oldFeature.getAutomatic());
				newFeature.cloneProperties(oldFeature);
			}
		}
	}

	public Configuration() {}

	public Configuration(FeatureModelFormula featureModel) {
		updateFeatures(featureModel);
	}

	public boolean updateFeatures(FeatureModelFormula featureModelFormula) {
		return updateFeatures(featureModelFormula, null);
	}

	public boolean updateFeatures(FeatureModelFormula featureModelFormula, List<Renaming> renamings) {
		if ((featureModelFormula != null) && (featureModel != featureModelFormula)) {
			initFeatures(featureModelFormula, renamings);
			return true;
		}
		return false;
	}

	private void initFeatures(FeatureModelFormula featureModelFormula, List<Renaming> renamings) {
		final IFeature featureRoot = FeatureUtils.getRoot(featureModelFormula.getFeatureModel());
		if (featureRoot != null) {
			featureModel = featureModelFormula;
			root = initFeatures(null, featureRoot, renamings);
			selectableFeatures.clear();
			readdFeatures(root);
		}
	}

	private SelectableFeature initFeatures(SelectableFeature parent, IFeature feature, List<Renaming> renamings) {
		final String curName = feature.getName();
		String oldName = curName;
		if (renamings != null) {
			for (final Renaming renaming : renamings) {
				if (renaming.newName.equals(curName)) {
					oldName = renaming.oldName;
					break;
				}
			}
		}
		SelectableFeature sFeature = selectableFeatures.get(oldName);
		if (sFeature == null) {
			sFeature = ConfigurationFactoryManager.getInstance().getFactory(this).createSelectableFeature(feature);
			selectableFeatures.put(curName, sFeature);
		} else if (!curName.equals(oldName)) {
			selectableFeatures.remove(oldName);
			sFeature = sFeature.clone();
			sFeature.setFeature(feature);
			sFeature.setName(null);
			selectableFeatures.put(curName, sFeature);
		} else if (sFeature.getFeature() == null) {
			sFeature.setFeature(feature);
			sFeature.setName(null);
		}

		sFeature.removeChildren();
		for (final IFeatureStructure child : feature.getStructure().getChildren()) {
			initFeatures(sFeature, child.getFeature(), renamings);
		}

		if (parent != null) {
			parent.addChild(sFeature);
		}
		return sFeature;
	}

	private void readdFeatures(SelectableFeature root) {
		selectableFeatures.put(root.getName(), root);
		for (final TreeElement child : root.getChildren()) {
			readdFeatures((SelectableFeature) child);
		}
	}

	public void resetAutomaticValues() {
		for (final SelectableFeature feature : selectableFeatures.values()) {
			feature.setAutomatic(Selection.UNDEFINED);
		}
	}

	public void setAutomatic(SelectableFeature feature, Selection selection) {
		feature.setAutomatic(selection);
	}

	public void setAutomatic(String name, Selection selection) {
		final SelectableFeature feature = getSelectableFeature(name, featureModel == null);
		if (feature == null) {
			throw new FeatureNotFoundException();
		}
		setAutomatic(feature, selection);
	}

	public IFeatureModel getFeatureModel() {
		return featureModel == null ? null : featureModel.getFeatureModel();
	}

	public FeatureModelFormula getFeatureModelFormula() {
		return featureModel;
	}

	public boolean hasFeatureModel() {
		return featureModel != null;
	}

	public Collection<SelectableFeature> getFeatures() {
		return Collections.unmodifiableCollection(selectableFeatures.values());
	}

	public List<SelectableFeature> getManualFeatures() {
		final List<SelectableFeature> featureList = new ArrayList<>();
		for (final SelectableFeature selectableFeature : selectableFeatures.values()) {
			if ((selectableFeature.getAutomatic() == Selection.UNDEFINED) && !selectableFeature.getFeature().getStructure().hasHiddenParent()) {
				featureList.add(selectableFeature);
			}
		}
		return featureList;
	}

	public List<SelectableFeature> getAutomaticFeatures() {
		final List<SelectableFeature> featureList = new ArrayList<>();
		for (final SelectableFeature selectableFeature : selectableFeatures.values()) {
			if ((selectableFeature.getAutomatic() != Selection.UNDEFINED) && !selectableFeature.getFeature().getStructure().hasHiddenParent()) {
				featureList.add(selectableFeature);
			}
		}
		return featureList;
	}

	public SelectableFeature getRoot() {
		return root;
	}

	public SelectableFeature getSelectableFeature(String name) {
		return getSelectableFeature(name, false);
	}

	public SelectableFeature getSelectableFeature(IFeature feature) {
		return selectableFeatures.get(feature.getName());
	}

	public SelectableFeature getSelectableFeature(String name, boolean create) {
		SelectableFeature selectableFeature = selectableFeatures.get(name);
		if (create && (selectableFeature == null)) {
			selectableFeature = ConfigurationFactoryManager.getInstance().getFactory(this).createSelectableFeature(null);
			selectableFeature.setName(name);
			selectableFeatures.put(name, selectableFeature);
		}
		return selectableFeature;
	}

	public Set<String> getSelectedFeatureNames() {
		final Set<String> result = new HashSet<String>();
		for (final SelectableFeature feature : selectableFeatures.values()) {
			if (feature.getSelection() == Selection.SELECTED) {
				result.add(feature.getName());
			}
		}
		return result;
	}

	public Set<String> getUnselectedFeatureNames() {
		final Set<String> result = new HashSet<String>();
		for (final SelectableFeature feature : selectableFeatures.values()) {
			if (feature.getSelection() == Selection.UNSELECTED) {
				result.add(feature.getName());
			}
		}
		return result;
	}

	public Set<String> getUndefinedFeatureNames() {
		final Set<String> result = new HashSet<String>();
		for (final SelectableFeature feature : selectableFeatures.values()) {
			if (feature.getSelection() == Selection.UNDEFINED) {
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
		for (final SelectableFeature feature : selectableFeatures.values()) {
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
		for (final SelectableFeature feature : selectableFeatures.values()) {
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
		for (final SelectableFeature feature : selectableFeatures.values()) {
			feature.setManual(Selection.UNDEFINED);
			feature.setAutomatic(Selection.UNDEFINED);
		}
	}

	public void reset() {
		selectableFeatures.clear();
		if (featureModel != null) {
			initFeatures(featureModel, null);
		}
	}

	public void setManual(SelectableFeature feature, Selection selection) {
		feature.setManual(selection);
	}

	public void setManual(String name, Selection selection) {
		final SelectableFeature feature = getSelectableFeature(name, featureModel == null);
		if (feature == null) {
			throw new FeatureNotFoundException();
		}
		setManual(feature, selection);
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		for (final SelectableFeature feature : selectableFeatures.values()) {
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

	public String getFactoryID() {
		return DefaultConfigurationFactory.ID;
	}

}
