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
package de.ovgu.featureide.fm.core.conf;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.conf.nodes.Variable;
import de.ovgu.featureide.fm.core.conf.nodes.VariableConfiguration;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.FeatureNotFoundException;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Represents a configuration and provides operations for the configuration process.
 *
 * @author Sebastian Krieter
 */
public class ConfigurationFG extends Configuration {

	private final class ToIFeature implements Functional.IFunction<IFeatureStructure, IFeature> {

		@Override
		public IFeature invoke(IFeatureStructure t) {
			return t.getFeature();
		}
	}

	public final static int PARAM_NONE = 0x00;
	public final static int PARAM_IGNOREABSTRACT = 0x02;
	public final static int PARAM_PROPAGATE = 0x04;
	public final static int PARAM_LAZY = 0x08;

	final ArrayList<SelectableFeature> features = new ArrayList<SelectableFeature>();
	final Hashtable<String, SelectableFeature> table = new Hashtable<String, SelectableFeature>();

	private final SelectableFeature root;
	private final String[] featureNames;

	private boolean propagate = true;

	private final IFeatureGraph featureGraph;
	private final VariableConfiguration variableConfiguration;
	private final ConfigurationChanger propagator;

	/**
	 * Creates a new configuration object.
	 *
	 * @param featureModel the corresponding feature model.
	 * @param options one or more of:</br> &nbsp;&nbsp;&nbsp;{@link #PARAM_IGNOREABSTRACT},</br> &nbsp;&nbsp;&nbsp;{@link #PARAM_LAZY},</br>
	 *        &nbsp;&nbsp;&nbsp;{@link #PARAM_PROPAGATE}
	 */
	public ConfigurationFG(IFeatureModel featureModel, IFeatureGraph featureGraph, int options) {
		super(featureModel);

		this.featureGraph = featureGraph;

		variableConfiguration = new VariableConfiguration(featureGraph.getSize());
		propagator = new ConfigurationChanger(featureGraph, featureModel, variableConfiguration, this);

		root = initRoot();

		featureNames = FeatureUtils.getFeaturesFromFeatureGraph(featureGraph);

		for (final String featureName : FeatureUtils.getCoreFeaturesFromFeatureGraph(featureGraph)) {
			setAutomatic(featureName, Selection.SELECTED);
		}

		for (final String featureName : FeatureUtils.getDeadFeaturesFromFeatureGraph(featureGraph)) {
			setAutomatic(featureName, Selection.UNSELECTED);
		}

		if ((options & PARAM_LAZY) != 0) {
			propagate = (options & PARAM_PROPAGATE) != 0;
		} else {
			loadPropagator((options & PARAM_PROPAGATE) != 0);
		}
	}

	private void initFeatures(SelectableFeature sFeature, IFeature feature) {
		if ((sFeature != null) && (sFeature.getName() != null)) {
			features.add(sFeature);
			table.put(sFeature.getName(), sFeature);
			for (final IFeature child : Functional.map(feature.getStructure().getChildren(), new ToIFeature())) {
				final SelectableFeature sChild = new SelectableFeature(child);
				sFeature.addChild(sChild);
				initFeatures(sChild, child);
			}
		}
	}

	private SelectableFeature initRoot() {
		final IFeature featureRoot = featureModel.getStructure().getRoot().getFeature();
		final SelectableFeature root = new SelectableFeature(featureRoot);

		if (featureRoot != null) {
			initFeatures(root, featureRoot);
		} else {
			features.add(root);
			table.put(root.getName(), root);
		}

		return root;
	}

	private void loadPropagator(boolean propagate) {
		LongRunningWrapper.runMethod(propagator.load());
		this.propagate = propagate;
		update(false, null);
	}

	@Override
	public ConfigurationChanger getPropagator() {
		return propagator;
	}

	@Override
	public void setAutomatic(SelectableFeature feature, Selection selection) {
		feature.setAutomatic(selection);
		final int featureIndex = featureGraph.getFeatureIndex(feature.getName());
		if (featureIndex >= 0) {
			variableConfiguration.setVariable(featureIndex, selection.getValue(), false);
		}
	}

	@Override
	public void setAutomatic(String name, Selection selection) {
		final SelectableFeature feature = table.get(name);
		if (feature == null) {
			throw new FeatureNotFoundException();
		}
		setAutomatic(feature, selection);
	}

	@Override
	public boolean canBeValid() {
		return LongRunningWrapper.runMethod(propagator.canBeValid());
	}

	@Override
	public IFeatureModel getFeatureModel() {
		return featureModel;
	}

	@Override
	public List<SelectableFeature> getFeatures() {
		return Collections.unmodifiableList(features);
	}

	@Override
	public List<SelectableFeature> getManualFeatures() {
		final List<SelectableFeature> featureList = new LinkedList<SelectableFeature>();
		for (final SelectableFeature selectableFeature : features) {
			if ((selectableFeature.getAutomatic() == Selection.UNDEFINED) && !selectableFeature.getFeature().getStructure().hasHiddenParent()) {
				featureList.add(selectableFeature);
			}
		}
		return featureList;
	}

	@Override
	public SelectableFeature getRoot() {
		return root;
	}

	@Override
	public SelectableFeature getSelectablefeature(String name) {
		return table.get(name);
	}

	@Override
	public Set<String> getSelectedFeatureNames() {
		final Set<String> result = new HashSet<String>();
		for (final SelectableFeature feature : features) {
			if (feature.getSelection() == Selection.SELECTED) {
				result.add(feature.getName());
			}
		}
		return result;
	}

	private IFeature getFeature(int id) {
		return featureModel.getFeature(featureNames[id]);
	}

	@Override
	public List<IFeature> getSelectedFeatures() {
		final String[] coreFeatures = FeatureUtils.getCoreFeaturesFromFeatureGraph(featureGraph);
		final List<IFeature> featureList = new ArrayList<>(variableConfiguration.size(true) + coreFeatures.length);
		for (final Variable var : variableConfiguration) {
			if (var.getValue() == Variable.TRUE) {
				featureList.add(getFeature(var.getId()));
			}
		}
		for (final String featureName : coreFeatures) {
			featureList.add(featureModel.getFeature(featureName));
		}
		return featureList;
	}

	@Override
	public List<List<String>> getSolutions(int max) throws TimeoutException {
		return LongRunningWrapper.runMethod(propagator.getSolutions(max));
	}

	@Override
	public List<IFeature> getUnSelectedFeatures() {
		final String[] deadFeatures = FeatureUtils.getDeadFeaturesFromFeatureGraph(featureGraph);
		final List<IFeature> featureList = new ArrayList<>(variableConfiguration.size(true) + deadFeatures.length);
		for (final Variable var : variableConfiguration) {
			if (var.getValue() == Variable.FALSE) {
				featureList.add(getFeature(var.getId()));
			}
		}
		for (final String featureName : deadFeatures) {
			featureList.add(featureModel.getFeature(featureName));
		}
		return featureList;
	}

	@Override
	public boolean isPropagate() {
		return propagate;
	}

	/**
	 * Checks that all manual and automatic selections are valid.<br> Abstract features will <b>not</b> be ignored.
	 *
	 * @return {@code true} if the current selection is a valid configuration
	 */
	@Override
	public boolean isValid() {
		if (propagator == null) {
			return true;
		}
		return LongRunningWrapper.runMethod(propagator.isValid());
	}

	/**
	 * Ignores hidden features. Use this, when propgate is disabled (hidden features are not updated).
	 */
	@Override
	public boolean isValidNoHidden() {
		return LongRunningWrapper.runMethod(propagator.isValidNoHidden());
	}

	@Override
	public void leadToValidConfiguration(List<SelectableFeature> featureList, IMonitor workMonitor) {}

	@Override
	public void leadToValidConfiguration(List<SelectableFeature> featureList, int mode, IMonitor workMonitor) {}

	/**
	 * Turns all automatic into manual values
	 *
	 * @param discardDeselected if {@code true} all automatic deselected features get undefined instead of manual deselected
	 */
	@Override
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

	@Override
	public long number(long timeout, boolean includeHiddenFeatures) {
		return LongRunningWrapper.runMethod(propagator.number(timeout, includeHiddenFeatures));
	}

	@Override
	public void resetValues() {
		for (final SelectableFeature feature : features) {
			feature.setManual(Selection.UNDEFINED);
			feature.setAutomatic(Selection.UNDEFINED);
		}
		variableConfiguration.reset();
		update(false, null);
	}

	@Override
	public void setManual(SelectableFeature feature, Selection selection) {
		feature.setManual(selection);
		final int featureIndex = featureGraph.getFeatureIndex(feature.getName());
		if (featureIndex >= 0) {
			variableConfiguration.setVariable(featureIndex, selection.getValue(), true);
		}
	}

	@Override
	public void setManual(String name, Selection selection) {
		final SelectableFeature feature = table.get(name);
		if (feature == null) {
			throw new FeatureNotFoundException();
		}
		setManual(feature, selection);
	}

	@Override
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

	@Override
	public void update(boolean redundantManual, List<SelectableFeature> featureOrder) {
		if (propagate) {
			LongRunningWrapper.runMethod(propagator.update(redundantManual, featureOrder));
		}
	}

}
