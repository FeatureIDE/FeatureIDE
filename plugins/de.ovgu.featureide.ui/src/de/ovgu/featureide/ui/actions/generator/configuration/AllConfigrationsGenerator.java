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
package de.ovgu.featureide.ui.actions.generator.configuration;

import java.util.LinkedList;

import org.eclipse.core.runtime.jobs.Job;
import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.SatSolver;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.ModelType;
import de.ovgu.featureide.fm.core.filter.AbstractFeatureFilter;
import de.ovgu.featureide.fm.core.job.IRunner;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor.MethodCancelException;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.actions.generator.ConfigurationBuilder;
import de.ovgu.featureide.ui.actions.generator.IConfigurationBuilderBasics;

/**
 * Configuration generator that creates all configurations of the feature model.<br> Exploits the structure of the feature model.
 *
 * @author Jens Meinicke
 */
public class AllConfigrationsGenerator extends AConfigurationGenerator {

	private IRunner<Boolean> number;

	/**
	 * @param builder
	 * @param featureModel
	 */
	public AllConfigrationsGenerator(final ConfigurationBuilder builder, final IFeatureModel featureModel, IFeatureProject featureProject) {
		super(builder, featureModel, featureProject);
		number = LongRunningWrapper.getRunner(new LongRunningMethod<Boolean>() {

			@Override
			public Boolean execute(IMonitor workMonitor) throws Exception {
				builder.configurationNumber = Math.min(new Configuration(featureModel, false, false).number(1000000, false), builder.configurationNumber);
				if (builder.configurationNumber < 0) {
					UIPlugin.getDefault().logWarning(StringTable.SATSOLVER_COMPUTATION_TIMEOUT);
					builder.configurationNumber = Math.min(Integer.MAX_VALUE, builder.configurationNumber);
				}
				return true;
			}
		}, IConfigurationBuilderBasics.JOB_TITLE_COUNT_CONFIGURATIONS);
		number.setPriority(Job.LONG);
		number.schedule();
	}

	private Node rootNode;
	private LinkedList<Node> children;

	/**
	 * The max size of <code>>configurations</code>
	 */
	private final int maxBufferSize = 5000;

	@Override
	public Void execute(IMonitor monitor) throws Exception {
		try {
			buildAll(featureModel.getStructure().getRoot().getFeature(), monitor);
		} finally {
			number.cancel();
		}
		return null;
	}

	/**
	 * Builds all possible valid configurations for the feature project.<br> Iterates through the structure of the feature model and ignores constraints, to get
	 * a linear expenditure.<br> After collecting a configurations the satsolver tests its validity.<br> Then the found configuration will be build into the
	 * folder for all valid products.
	 *
	 * @param root The root feature of the feature model
	 * @param monitor
	 */
	private void buildAll(IFeature root, IMonitor monitor) {
		final LinkedList<IFeature> selectedFeatures2 = new LinkedList<IFeature>();
		selectedFeatures2.add(root);
		rootNode = AdvancedNodeCreator.createNodes(featureModel, new AbstractFeatureFilter(), CNFType.Compact, ModelType.All, true);
		children = new LinkedList<Node>();
		build(root, "", selectedFeatures2, monitor);
	}

	// TODO use intermediate function of monitor object instead of producer-consumer pattern
	private void build(IFeature currentFeature, String selected, LinkedList<IFeature> selectedFeatures2, IMonitor monitor) {
		try {
			monitor.checkCancel();
		} catch (final MethodCancelException e) {
			number.cancel();
			cancelGenerationJobs();
			return;
		}
		if (confs >= maxConfigs()) {
			return;
		}

		if (featureModel.getConstraintCount() > 0) {
			children.clear();
			for (final String feature : selected.split("\"")) {
				children.add(new Literal(feature, true));
			}
			try {
				if (!(new SatSolver(new And(rootNode.clone(), new And(children)), 1000)).isSatisfiable()) {
					return;
				}
			} catch (final org.sat4j.specs.TimeoutException e) {
				UIPlugin.getDefault().logError(e);
			}
		}

		if (selectedFeatures2.isEmpty()) {
			configuration.resetValues();

			if (!selected.isEmpty()) {
				for (final String feature : selected.split("\"")) {
					configuration.setManual((feature), Selection.SELECTED);
				}

			}
			if (configuration.isValid()) {
				final LinkedList<String> selectedFeatures3 = new LinkedList<String>();
				for (final String f : selected.split("\"")) {
					if (!"".equals(f)) {
						selectedFeatures3.add(f);
					}
				}
				for (final IFeature f : configuration.getSelectedFeatures()) {
					if (isSelectable(f)) {
						if (!selectedFeatures3.contains(f.getName())) {
							return;
						}
					}
				}
				for (final String f : selectedFeatures3) {
					if (configuration.getSelectablefeature(f).getSelection() != Selection.SELECTED) {
						return;
					}
				}

				addConfiguration(configuration);

				if (builder.sorter.getBufferSize() >= maxBufferSize) {
					synchronized (this) {
						while (builder.sorter.getBufferSize() >= maxBufferSize) {
							try {
								monitor.checkCancel();
							} catch (final MethodCancelException e) {
								number.cancel();
								return;
							}
							try {
								wait(1000);
							} catch (final InterruptedException e) {
								UIPlugin.getDefault().logError(e);
							}
						}
					}
				}
			}
			return;
		}

		if (currentFeature.getStructure().isAnd()) {
			buildAnd(selected, selectedFeatures2, monitor);
		} else if (currentFeature.getStructure().isOr()) {
			buildOr(selected, selectedFeatures2, monitor);
		} else if (currentFeature.getStructure().isAlternative()) {
			buildAlternative(selected, selectedFeatures2, monitor);
		}
	}

	private void buildAlternative(String selected, LinkedList<IFeature> selectedFeatures2, IMonitor monitor) {
		IFeature currentFeature = selectedFeatures2.getFirst();
		selectedFeatures2.removeFirst();
		LinkedList<IFeature> selectedFeatures3 = new LinkedList<IFeature>();
		if (isSelectable(currentFeature)) {
			if ("".equals(selected)) {
				selected = currentFeature.getName();
			} else {
				selected += "\"" + currentFeature.getName();
			}
		}
		if (!currentFeature.getStructure().hasChildren()) {
			if (selectedFeatures2.isEmpty()) {
				currentFeature = null;
			} else {
				currentFeature = selectedFeatures2.getFirst();
			}
			selectedFeatures3.addAll(selectedFeatures2);
			build(currentFeature, selected, selectedFeatures3, monitor);
			return;
		}
		for (int i2 = 0; i2 < getChildren(currentFeature).size(); i2++) {
			selectedFeatures3 = new LinkedList<IFeature>();
			selectedFeatures3.add(getChildren(currentFeature).get(i2));
			selectedFeatures3.addAll(selectedFeatures2);
			build(selectedFeatures3.isEmpty() ? null : selectedFeatures3.getFirst(), selected, selectedFeatures3, monitor);
		}
	}

	private void buildOr(String selected, LinkedList<IFeature> selectedFeatures2, IMonitor monitor) {
		IFeature currentFeature = selectedFeatures2.getFirst();
		selectedFeatures2.removeFirst();
		LinkedList<IFeature> selectedFeatures3 = new LinkedList<IFeature>();
		if (isSelectable(currentFeature)) {
			if ("".equals(selected)) {
				selected = currentFeature.getName();
			} else {
				selected += "\"" + currentFeature.getName();
			}
		}
		if (!currentFeature.getStructure().hasChildren()) {
			if (selectedFeatures2.isEmpty()) {
				currentFeature = null;
			} else {
				currentFeature = selectedFeatures2.getFirst();
			}
			selectedFeatures3.addAll(selectedFeatures2);
			build(currentFeature, selected, selectedFeatures3, monitor);
			return;
		}
		final LinkedList<IFeature> children2 = getChildren(currentFeature);
		for (int i2 = (int) java.lang.Math.pow(2, children2.size()) - 1; i2 > 0; i2--) {
			int k2 = i2;
			selectedFeatures3 = new LinkedList<IFeature>();
			for (int j = 0; j < children2.size(); j++) {
				if ((k2 % 2) != 0) {
					selectedFeatures3.add(children2.get(j));
				}
				k2 = k2 / 2;
			}
			selectedFeatures3.addAll(selectedFeatures2);
			build(selectedFeatures3.isEmpty() ? null : selectedFeatures3.getFirst(), selected, selectedFeatures3, monitor);
		}
	}

	private void buildAnd(String selected, LinkedList<IFeature> selectedFeatures2, IMonitor monitor) {
		IFeature currentFeature = selectedFeatures2.removeFirst();
		LinkedList<IFeature> selectedFeatures3 = new LinkedList<IFeature>();
		if (isSelectable(currentFeature)) {
			if ("".equals(selected)) {
				selected = currentFeature.getName();
			} else {
				selected += "\"" + currentFeature.getName();
			}
		}
		if (!currentFeature.getStructure().hasChildren()) {
			if (selectedFeatures2.isEmpty()) {
				currentFeature = null;
			} else {
				currentFeature = selectedFeatures2.getFirst();
			}
			selectedFeatures3.addAll(selectedFeatures2);
			build(currentFeature, selected, selectedFeatures3, monitor);
			return;
		}
		int k2;
		final LinkedList<IFeature> optionalFeatures = new LinkedList<IFeature>();
		for (final IFeature f : getChildren(currentFeature)) {
			if (f.getStructure().isMandatory()) {
				selectedFeatures2.add(f);
			} else {
				optionalFeatures.add(f);
			}
		}

		for (int i2 = 0; i2 < (int) java.lang.Math.pow(2, optionalFeatures.size()); i2++) {
			k2 = i2;
			selectedFeatures3 = new LinkedList<IFeature>();
			for (int j = 0; j < optionalFeatures.size(); j++) {
				if ((k2 % 2) != 0) {
					selectedFeatures3.add(optionalFeatures.get(j));
				}
				k2 = k2 / 2;
			}
			selectedFeatures3.addAll(selectedFeatures2);
			build(selectedFeatures3.isEmpty() ? null : selectedFeatures3.getFirst(), selected, selectedFeatures3, monitor);
		}

	}

	/**
	 * Returns all children of a feature if it is a layer or if it has a child that is concrete.
	 *
	 * @param currentFeature The feature
	 * @return The children
	 */
	private LinkedList<IFeature> getChildren(IFeature currentFeature) {
		final LinkedList<IFeature> children = new LinkedList<IFeature>();
		for (final IFeatureStructure childStructure : currentFeature.getStructure().getChildren()) {
			final IFeature child = childStructure.getFeature();
			if (isSelectable(child) || hasLayerChild(child)) {
				children.add(child);
			}
		}
		return children;
	}

	/**
	 * @param feature The feature
	 * @return <code>true</code> if the feature is a layer or if it has a child that is a concrete
	 */
	private boolean hasLayerChild(IFeature feature) {
		if (feature.getStructure().hasChildren()) {
			for (final IFeatureStructure childStructure : feature.getStructure().getChildren()) {
				final IFeature child = childStructure.getFeature();
				if (isSelectable(child) || hasLayerChild(child)) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Checks whether the concrete feature can be selected manually.
	 */
	private boolean isSelectable(final IFeature child) {
		final IFeatureStructure structure = child.getStructure();
		final boolean concrete = structure.isConcrete();
		return concrete && !structure.isHidden();
	}

}
