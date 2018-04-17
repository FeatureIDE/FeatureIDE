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
import java.util.Hashtable;
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

	public final static int PARAM_NONE = 0x00;
	public final static int PARAM_IGNOREABSTRACT = 0x02;
	public final static int PARAM_PROPAGATE = 0x04;
	public final static int PARAM_LAZY = 0x08;

	final ArrayList<SelectableFeature> features = new ArrayList<SelectableFeature>();
	final Hashtable<String, SelectableFeature> table = new Hashtable<String, SelectableFeature>();

	final boolean ignoreAbstractFeatures;

	protected final IFeatureModel featureModel;
	private final SelectableFeature root;
	private final ConfigurationPropagator propagator;
	private boolean propagate = true;

	/**
	 * This method creates a clone of the given {@link Configuration}
	 *
	 * @param configuration The configuration to clone
	 */
	protected Configuration(Configuration configuration) {
		featureModel = configuration.featureModel;
		ignoreAbstractFeatures = configuration.ignoreAbstractFeatures;
		propagator = configuration.propagator.clone(this);
		propagate = false;
		root = initRoot();

		for (final SelectableFeature f : configuration.features) {
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
	 * @param propagate
	 */
	public Configuration(Configuration configuration, IFeatureModel featureModel) {
		this.featureModel = featureModel;
		ignoreAbstractFeatures = configuration.ignoreAbstractFeatures;
		propagator = new ConfigurationPropagator(this);
		propagate = false;
		root = initRoot();

		for (final SelectableFeature oldFeature : configuration.features) {
			final SelectableFeature newFeature = table.get(oldFeature.getName());
			if (newFeature != null) {
				newFeature.setManual(oldFeature.getManual());
			}
		}
	}

	public Configuration(IFeatureModel featureModel) {
		this(featureModel, PARAM_PROPAGATE | PARAM_IGNOREABSTRACT);
	}

	public Configuration(IFeatureModel featureModel, boolean propagate) {
		this(featureModel, (propagate ? PARAM_PROPAGATE : 0) | PARAM_IGNOREABSTRACT);
	}

	public Configuration(IFeatureModel featureModel, boolean propagate, boolean ignoreAbstractFeatures) {
		this(featureModel, (propagate ? PARAM_PROPAGATE : 0) | (ignoreAbstractFeatures ? PARAM_IGNOREABSTRACT : 0));
	}

	/**
	 * Creates a new configuration object.
	 *
	 * @param featureModel the corresponding feature model.
	 * @param options one or more of:</br> &nbsp;&nbsp;&nbsp;{@link #PARAM_IGNOREABSTRACT},</br> &nbsp;&nbsp;&nbsp;{@link #PARAM_LAZY},</br>
	 *        &nbsp;&nbsp;&nbsp;{@link #PARAM_PROPAGATE}
	 */
	public Configuration(IFeatureModel featureModel, int options) {
		this.featureModel = featureModel;
		ignoreAbstractFeatures = (options & PARAM_IGNOREABSTRACT) != 0;
		propagate = (options & PARAM_PROPAGATE) != 0;
		propagator = new ConfigurationPropagator(this);
		root = initRoot();

		if ((options & PARAM_LAZY) == 0) {
			loadPropagator();
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

	public void loadPropagator() {
		LongRunningWrapper.runMethod(propagator.load());
		update(true, null);
	}

	public IConfigurationPropagator getPropagator() {
		return propagator;
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

	public boolean canBeValid() {
		return LongRunningWrapper.runMethod(propagator.canBeValid());
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

	public SelectableFeature getSelectablefeature(String name) {
		return table.get(name);
	}

	public Set<String> getSelectedFeatureNames() {
		final Set<String> result = new HashSet<String>();
		for (final SelectableFeature feature : features) {
			if (feature.getSelection() == Selection.SELECTED) {
				result.add(feature.getName());
			}
		}
		return result;
	}

	public List<IFeature> getSelectedFeatures() {
		final List<IFeature> result = new ArrayList<IFeature>();
		for (final SelectableFeature feature : features) {
			if (feature.getSelection() == Selection.SELECTED) {
				result.add(feature.getFeature());
			}
		}
		return result;
	}

	public List<List<String>> getSolutions(int max) throws TimeoutException {
		return LongRunningWrapper.runMethod(propagator.getSolutions(max));
	}

	public List<IFeature> getUnSelectedFeatures() {
		final List<IFeature> result = new ArrayList<IFeature>();
		for (final SelectableFeature feature : features) {
			if (feature.getSelection() == Selection.UNSELECTED) {
				result.add(feature.getFeature());
			}
		}

		return result;
	}

	public List<IFeature> getUndefinedSelectedFeatures() {
		final List<IFeature> result = new ArrayList<IFeature>();
		for (final SelectableFeature feature : features) {
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
		return LongRunningWrapper.runMethod(propagator.isValid());
	}

	/**
	 * Ignores hidden features. Use this, when propgate is disabled (hidden features are not updated).
	 */
	public boolean isValidNoHidden() {
		return LongRunningWrapper.runMethod(propagator.isValidNoHidden());
	}

	public void leadToValidConfiguration(List<SelectableFeature> featureList, IMonitor workMonitor) {
		LongRunningWrapper.runMethod(propagator.leadToValidConfiguration(featureList));
	}

	public void leadToValidConfiguration(List<SelectableFeature> featureList, int mode, IMonitor workMonitor) {
		LongRunningWrapper.runMethod(propagator.leadToValidConfiguration(featureList, mode));
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

	/**
	 * Convenience method, fully equivalent to {@link #number(long, boolean) number(250, false)}.
	 *
	 * @return number of possible solutions
	 *
	 * @see #number(long)
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
	 * @return a positive value equal to the number of solutions (if the method terminated in time)</br> or a negative value (if a timeout occured) that
	 *         indicates that there are more solutions than the absolute value
	 */
	public long number(long timeout, boolean includeHiddenFeatures) {
		return LongRunningWrapper.runMethod(propagator.number(timeout, includeHiddenFeatures));
	}

	public void resetValues() {
		for (final SelectableFeature feature : features) {
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
		final SelectableFeature feature = table.get(name);
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
		for (final SelectableFeature feature : features) {
			if ((feature.getSelection() == Selection.SELECTED) && feature.getFeature().getStructure().isConcrete()) {
				builder.append(feature.getFeature().getName());
				builder.append("\n");
			}
		}
		return builder.toString();
	}

	public void update(boolean redundantManual, List<SelectableFeature> featureOrder) {
		if (propagate) {
			LongRunningWrapper.runMethod(propagator.update(redundantManual, featureOrder));
		}
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
		return LongRunningWrapper.runMethod(propagator.coverFeatures(features, selection), monitor);

	}

	public boolean isIgnoreAbstractFeatures() {
		return ignoreAbstractFeatures;
	}

}
