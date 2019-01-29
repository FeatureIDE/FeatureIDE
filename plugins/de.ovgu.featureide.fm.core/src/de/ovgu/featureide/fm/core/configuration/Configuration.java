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
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Set;

import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Represents a configuration and provides operations for the configuration process.
 */
public class Configuration implements Cloneable {

	protected final LinkedHashMap<String, SelectableFeature> selectableFeatures = new LinkedHashMap<>();

	protected IFeatureModel featureModel;
	protected SelectableFeature root;
	protected ConfigurationPropagator propagator;
	protected boolean considerAbstractFeatures;
	protected boolean propagate;

	/**
	 * This method creates a clone of the given {@link Configuration}
	 *
	 * @param configuration The configuration to clone
	 */
	protected Configuration(Configuration configuration) {
		considerAbstractFeatures = configuration.considerAbstractFeatures;

		propagate = false;
		initFeatures(configuration.featureModel);
		for (final SelectableFeature f : configuration.selectableFeatures.values()) {
			setManual(f.getName(), f.getManual());
			setAutomatic(f.getName(), f.getAutomatic());
		}
		propagate = configuration.propagate;
	}

	/**
	 * Copy constructor. Copies the status of a given configuration.
	 *
	 * @param configuration
	 * @param featureModel the underlying feature model. The model can be different from the old configuration.
	 */
	public Configuration(Configuration configuration, IFeatureModel featureModel) {
		considerAbstractFeatures = configuration.considerAbstractFeatures;

		propagate = false;
		initFeatures(featureModel);
		for (final SelectableFeature oldFeature : configuration.selectableFeatures.values()) {
			final SelectableFeature newFeature = selectableFeatures.get(oldFeature.getName());
			if (newFeature != null) {
				newFeature.setManual(oldFeature.getManual());
			}
		}
	}

	public Configuration() {
		this(null, true, true);
	}

	public Configuration(IFeatureModel featureModel) {
		this(featureModel, true, true);
	}

	public Configuration(IFeatureModel featureModel, boolean propagate) {
		this(featureModel, propagate, true);
	}

	public Configuration(IFeatureModel featureModel, boolean propagate, boolean considerAbstractFeatures) {
		this.considerAbstractFeatures = considerAbstractFeatures;
		this.propagate = propagate;
		initFeatures(featureModel);
	}

	public void initFeatures(IFeatureModel featureModel) {
		if (updateFeatures(featureModel) && propagate) {
			update();
		}
	}

	public boolean updateFeatures(IFeatureModel featureModel) {
		if ((featureModel != null) && (this.featureModel != featureModel)) {
			final IFeature featureRoot = FeatureUtils.getRoot(featureModel);
			if (featureRoot != null) {
				this.featureModel = featureModel;
				propagator = null;
				root = initFeatures(null, featureRoot);
				selectableFeatures.clear();
				readdFeatures(root);
			}
			return true;
		}
		return false;
	}

	private SelectableFeature initFeatures(SelectableFeature parent, IFeature feature) {
		SelectableFeature sFeature = selectableFeatures.get(featureModel.getRenamingsManager().getOldName(feature.getName()));
		if (sFeature == null) {
			sFeature = new SelectableFeature(feature);
			selectableFeatures.put(feature.getName(), sFeature);
		} else if (sFeature.getFeature() == null) {
			sFeature.setFeature(feature);
			sFeature.setName(null);
		}

		sFeature.removeChildren();
		for (final IFeatureStructure child : feature.getStructure().getChildren()) {
			initFeatures(sFeature, child.getFeature());
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

	private ConfigurationPropagator propagator() {
		if ((propagator == null) || !propagator.isLoaded()) {
			propagator = new ConfigurationPropagator(this);
			if (featureModel != null) {
				LongRunningWrapper.runMethod(propagator.load());
			}
		}
		return propagator;
	}

	public IConfigurationPropagator getPropagator() {
		if (propagator == null) {
			propagator = new ConfigurationPropagator(this);
		}
		return propagator;
	}

	void resetAutomaticValues() {
		for (final SelectableFeature feature : selectableFeatures.values()) {
			feature.setAutomatic(Selection.UNDEFINED);
		}
	}

	public void setAutomatic(SelectableFeature feature, Selection selection) {
		feature.setAutomatic(selection);
	}

	public void setAutomatic(String name, Selection selection) {
		final SelectableFeature feature = selectableFeatures.get(name);
		if (feature == null) {
			throw new FeatureNotFoundException();
		}
		setAutomatic(feature, selection);
	}

	public boolean canBeValid() {
		return LongRunningWrapper.runMethod(propagator().canBeValid());
	}

	public IFeatureModel getFeatureModel() {
		return featureModel;
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

	public SelectableFeature getRoot() {
		return root;
	}

	public SelectableFeature getSelectableFeature(String name) {
		return selectableFeatures.get(name);
	}

	public SelectableFeature getSelectableFeature(IFeature feature) {
		return selectableFeatures.get(feature.getName());
	}

	public SelectableFeature getSelectableFeature(String name, boolean create) {
		SelectableFeature selectableFeature = selectableFeatures.get(name);
		if (create && (selectableFeature == null)) {
			selectableFeature = new SelectableFeature(name);
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

	public List<IFeature> getSelectedFeatures() {
		final List<IFeature> result = new ArrayList<IFeature>();
		for (final SelectableFeature feature : selectableFeatures.values()) {
			if (feature.getSelection() == Selection.SELECTED) {
				result.add(feature.getFeature());
			}
		}
		return result;
	}

	public List<List<String>> getSolutions(int max) throws TimeoutException {
		return LongRunningWrapper.runMethod(propagator().getSolutions(max));
	}

	public List<IFeature> getUnSelectedFeatures() {
		final List<IFeature> result = new ArrayList<IFeature>();
		for (final SelectableFeature feature : selectableFeatures.values()) {
			if (feature.getSelection() == Selection.UNSELECTED) {
				result.add(feature.getFeature());
			}
		}

		return result;
	}

	public List<IFeature> getUndefinedSelectedFeatures() {
		final List<IFeature> result = new ArrayList<IFeature>();
		for (final SelectableFeature feature : selectableFeatures.values()) {
			if (feature.getSelection() == Selection.UNDEFINED) {
				result.add(feature.getFeature());
			}
		}

		return result;
	}

	public boolean isPropagate() {
		return propagate;
	}

	/**
	 * Checks that all manual and automatic selections are valid.<br> Abstract features will <b>not</b> be ignored.
	 *
	 * @return {@code true} if the current selection is a valid configuration
	 */
	public boolean isValid() {
		return LongRunningWrapper.runMethod(propagator().isValid());
	}

	/**
	 * Ignores hidden features. Use this, when propgate is disabled (hidden features are not updated).
	 */
	public boolean isValidNoHidden() {
		return LongRunningWrapper.runMethod(propagator().isValidNoHidden());
	}

	public void leadToValidConfiguration(List<SelectableFeature> featureList, IMonitor workMonitor) {
		LongRunningWrapper.runMethod(propagator().leadToValidConfiguration(featureList));
	}

	public void leadToValidConfiguration(List<SelectableFeature> featureList, int mode, IMonitor workMonitor) {
		LongRunningWrapper.runMethod(propagator().leadToValidConfiguration(featureList, mode));
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

	/**
	 * Convenience method, fully equivalent to {@link #number(long, boolean) number(250, false)}.
	 *
	 * @return number of possible solutions
	 *
	 * @see #number(boolean)
	 * @see #number(long, boolean)
	 */
	public long number() {
		return number(250, false);
	}

	/**
	 * Convenience method, fully equivalent to {@link #number(long, boolean) number(250, includeHiddenFeatures)}.
	 *
	 * @param includeHiddenFeatures {@code true} if hidden feature should be considered, {@code false} otherwise
	 *
	 * @return number of possible solutions
	 *
	 * @see #number()
	 * @see #number(long, boolean)
	 */
	public long number(boolean includeHiddenFeatures) {
		return number(250, includeHiddenFeatures);
	}

	/**
	 * Counts the number of possible solutions.
	 *
	 * @param timeout Timeout in milliseconds.
	 * @param includeHiddenFeatures {@code true} if hidden feature should be considered, {@code false} otherwise
	 *
	 * @return a positive value equal to the number of solutions (if the method terminated in time)<br> or a negative value (if a timeout occured) that
	 *         indicates that there are more solutions than the absolute value
	 */
	public long number(long timeout, boolean includeHiddenFeatures) {
		return LongRunningWrapper.runMethod(propagator().number(timeout, includeHiddenFeatures));
	}

	public void resetValues() {
		for (final SelectableFeature feature : selectableFeatures.values()) {
			feature.setManual(Selection.UNDEFINED);
			feature.setAutomatic(Selection.UNDEFINED);
		}
		update(false, null);
	}

	public void setManual(SelectableFeature feature, Selection selection) {
		feature.setManual(selection);
		update(true, Arrays.asList(feature));
	}

	public void setManual(String name, Selection selection) {
		final SelectableFeature feature = selectableFeatures.get(name);
		if (feature == null) {
			throw new FeatureNotFoundException();
		}
		setManual(feature, selection);
	}

	public void setPropagate(boolean propagate) {
		this.propagate = propagate;
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

	public void update() {
		LongRunningWrapper.runMethod(propagator().update(false, null));
	}

	public void update(boolean redundantManual, List<SelectableFeature> featureOrder) {
		if (propagate) {
			LongRunningWrapper.runMethod(propagator().update(redundantManual, featureOrder));
		}
	}

	public void resolve() {
		LongRunningWrapper.runMethod(propagator().resolve());
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

	/**
	 * Creates solutions to cover the given features.
	 *
	 * @param features The features that should be covered.
	 * @param selection true is the features should be selected, false otherwise.
	 */
	public List<List<String>> coverFeatures(Collection<String> features, IMonitor monitor, boolean selection) throws TimeoutException {
		return LongRunningWrapper.runMethod(propagator().coverFeatures(features, selection), monitor);

	}

	public void setConsiderAbstractFeatures(boolean considerAbstractFeatures) {
		this.considerAbstractFeatures = considerAbstractFeatures;
	}

	public boolean isIgnoreAbstractFeatures() {
		return considerAbstractFeatures;
	}

}
