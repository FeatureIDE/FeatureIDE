/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.job.WorkMonitor;

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

	private final FeatureModel featureModel;
	private final SelectableFeature root;
	private final ConfigurationPropagator propagator;
	private boolean propagate = true;

	/**
	 * This method creates a clone of the given {@link Configuration}
	 * @param configuration The configuration to clone
	 */
	protected Configuration(Configuration configuration) {
		this.featureModel = configuration.featureModel;
		this.ignoreAbstractFeatures = configuration.ignoreAbstractFeatures;
		this.propagator = configuration.propagator.clone(this);
		propagate = false;
		this.root = initRoot();
		
		for (SelectableFeature f : configuration.features) {
			setManual(f.getName(), f.getManual());
			setAutomatic(f.getName(), f.getAutomatic());
		}
		this.propagate = configuration.propagate;
	}

	/**
	 * Copy constructor. Copies the status of a given configuration.
	 * @param configuration
	 * @param featureModel the underlying feature model. The model can be different from the old configuration.
	 * @param propagate
	 */
	public Configuration(Configuration configuration, FeatureModel featureModel) {
		this.featureModel = featureModel;
		this.ignoreAbstractFeatures = configuration.ignoreAbstractFeatures;
		this.propagator = new ConfigurationPropagator(this);
		this.propagate = false;
		this.root = initRoot();
		
		for (SelectableFeature f : configuration.features) {
			try {
				setManual(f.getName(), (f.getManual()));
			} catch (FeatureNotFoundException e) {
			}
		}

		loadPropagator(configuration.propagate);
	}
	
	public Configuration(FeatureModel featureModel) {
		this(featureModel, PARAM_PROPAGATE | PARAM_IGNOREABSTRACT);
	}
	
	public Configuration(FeatureModel featureModel, boolean propagate) {
		this(featureModel, (propagate ? PARAM_PROPAGATE : 0) | PARAM_IGNOREABSTRACT);
	}
	
	public Configuration(FeatureModel featureModel, boolean propagate, boolean ignoreAbstractFeatures) {
		this(featureModel, (propagate ? PARAM_PROPAGATE : 0) | (ignoreAbstractFeatures ? PARAM_IGNOREABSTRACT : 0));
	}
	
	/**
	 * Creates a new configuration object.
	 * @param featureModel the corresponding feature model.
	 * @param options one or more of:</br>
	 * 	&nbsp;&nbsp;&nbsp;{@link #PARAM_IGNOREABSTRACT},</br>
	 *  &nbsp;&nbsp;&nbsp;{@link #PARAM_LAZY},</br>
	 *  &nbsp;&nbsp;&nbsp;{@link #PARAM_PROPAGATE}
	 */
	public Configuration(FeatureModel featureModel, int options) {
		this.featureModel = featureModel;
		this.ignoreAbstractFeatures = (options & PARAM_IGNOREABSTRACT) != 0;
		this.propagator = new ConfigurationPropagator(this);
		this.root = initRoot();
		
		if ((options & PARAM_LAZY) != 0) {
			this.propagate = (options & PARAM_PROPAGATE) != 0;
		} else {
			loadPropagator((options & PARAM_PROPAGATE) != 0);
		}
	}
	
	private void initFeatures(SelectableFeature sFeature, Feature feature) {
		if (sFeature != null && sFeature.getName() != null) {
			features.add(sFeature);
			table.put(sFeature.getName(), sFeature);
			for (Feature child : feature.getChildren()) {
				SelectableFeature sChild = new SelectableFeature(this, child);
				sFeature.addChild(sChild);
				initFeatures(sChild, child);
			}
		}
	}

	private SelectableFeature initRoot() {
		final Feature featureRoot = featureModel.getRoot();
		final SelectableFeature root = new SelectableFeature(this, featureRoot);
		
		if (featureRoot != null) {
			initFeatures(root, featureRoot);
		} else {
			features.add(root);
			table.put(root.getName(), root);
		}
		
		return root;
	}

	private void loadPropagator(boolean propagate) {
		this.propagator.load(new WorkMonitor());
		this.propagate = propagate;
		update(false, null);
	}
	
	public ConfigurationPropagator getPropagator() {
		return propagator;
	}

	void resetAutomaticValues() {
		for (SelectableFeature feature : features) {
			feature.setAutomatic(Selection.UNDEFINED);
		}
	}
	
	void setAutomatic(SelectableFeature feature, Selection selection) {
		feature.setAutomatic(selection);
	}
	
	void setAutomatic(String name, Selection selection) {
		SelectableFeature feature = table.get(name);
		if (feature == null) {
			throw new FeatureNotFoundException();
		}
		setAutomatic(feature, selection);
	}
	
	public boolean canBeValid() {
		return propagator.canBeValid(new WorkMonitor());
	}

	public FeatureModel getFeatureModel() {
		return featureModel;
	}
	
	public List<SelectableFeature> getFeatures() {
		return Collections.unmodifiableList(features);
	}

	public List<SelectableFeature> getManualFeatures() {
		final List<SelectableFeature> featureList = new LinkedList<SelectableFeature>();
		for (SelectableFeature selectableFeature : features) {
			if (selectableFeature.getAutomatic() == Selection.UNDEFINED && !selectableFeature.getFeature().hasHiddenParent()) {
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
		for (SelectableFeature feature : features) {
			if (feature.getSelection() == Selection.SELECTED) {
				result.add(feature.getName());
			}
		}
		return result;
	}
	
	public List<Feature> getSelectedFeatures() {
		final List<Feature> result = new ArrayList<Feature>();
		for (SelectableFeature feature : features) {
			if (feature.getSelection() == Selection.SELECTED) {
				result.add(feature.getFeature());
			}
		}
		return result;
	}
	
	public LinkedList<List<String>> getSolutions(int max) throws TimeoutException {
		return propagator.getSolutions(max, new WorkMonitor());
	}
	
	public List<Feature> getUnSelectedFeatures() {
		final List<Feature> result = new ArrayList<Feature>();
		
		for (SelectableFeature feature : features) {
			if (feature.getSelection() == Selection.UNSELECTED) {
				result.add(feature.getFeature());
			}
		}
		
		return result;
	}
	
	public boolean isPropagate() {
		return this.propagate;
	}

	/**
	 * Checks that all manual and automatic selections are valid.<br>
	 * Abstract features will <b>not</b> be ignored.
	 * @return  {@code true} if the current selection is a valid configuration
	 */
	public boolean isValid() {
		return propagator.isValid(new WorkMonitor());
	}
	
	/**
	 * Ignores hidden features.
	 * Use this, when propgate is disabled (hidden features are not updated).
	 */
	public boolean isValidNoHidden() {
		return propagator.isValidNoHidden(new WorkMonitor());
	}
	
	public void leadToValidConfiguration(List<SelectableFeature> featureList, WorkMonitor workMonitor) {
		propagator.leadToValidConfiguration(featureList, new WorkMonitor());
	}
	
	public void leadToValidConfiguration(List<SelectableFeature> featureList, int mode, WorkMonitor workMonitor) {
		propagator.leadToValidConfiguration(featureList, mode, new WorkMonitor());
	}

	/**
	 * Turns all automatic into manual values
	 * @param discardDeselected if {@code true} all automatic deselected features get undefined instead of manual deselected
	 */
	public void makeManual(boolean discardDeselected) {
		for (SelectableFeature feature : features) {
			final Selection autoSelection = feature.getAutomatic();
			if (autoSelection != Selection.UNDEFINED) {
				feature.setAutomatic(Selection.UNDEFINED);
				if (!discardDeselected || autoSelection == Selection.SELECTED) {
					feature.setManual(autoSelection);
				}
			}
		}
	}

	/**
	 * Convenience method.
	 * @return the values of number(250)
	 * @see #number(long)
	 */
	public long number() {
		return propagator.number(250, new WorkMonitor());
	}
	
	/**
	 * Counts the number of possible solutions.
	 * @return a positive value equal to the number of solutions (if the method terminated in time)</br>
	 * 	or a negative value (if a timeout occured) that indicates that there are more solutions than the absolute value
	 */
	public long number(long timeout) {
		return propagator.number(timeout, new WorkMonitor());
	}

	public void resetValues() {
		for (SelectableFeature feature : features) {
			feature.setManual(Selection.UNDEFINED);
			feature.setAutomatic(Selection.UNDEFINED);
		}
		update(false, null);
	}
	
	public void setManual(SelectableFeature feature, Selection selection) {
		feature.setManual(selection);
		update(false, null);
	}

	public void setManual(String name, Selection selection) {
		SelectableFeature feature = table.get(name);
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
		StringBuilder builder = new StringBuilder();
		for (SelectableFeature feature : features) {
			if (feature.getSelection() == Selection.SELECTED && feature.getFeature().isConcrete()) {
				builder.append(feature.getFeature().getName());
				builder.append("\n");
			}
		}
		return builder.toString();
	}
	
	public void update() {
		update(false, null);
	}
	
	public void update(boolean redundantManual, String startFeatureName) {
		if (propagate) {
			propagator.update(redundantManual, startFeatureName, new WorkMonitor());
		}
	}

	@Override
	public Configuration clone() {
		if (!this.getClass().equals(Configuration.class)) {
			try {
				return (Configuration) super.clone();
			} catch (CloneNotSupportedException e) {
				FMCorePlugin.getDefault().logError(e);
			}
		}
		return new Configuration(this);
	}
	
}
