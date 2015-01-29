/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.Preferences;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.job.WorkMonitor;

/**
 * Represents a configuration and provides operations for the configuration process.
 */
public class ConfigurationPropagator {
	
	private static class BuildThread extends Thread {
		private final FeatureModel featureModel;
		private final Set<String> featureSet;
		private final boolean ignoreAbstractFeatures;
		private Node buildNode;
		
		public BuildThread(FeatureModel featureModel, Set<String> featureSet) {
			super();
			this.featureModel = featureModel;
			this.featureSet = featureSet;
			this.ignoreAbstractFeatures = false;
		}
		
		public BuildThread(FeatureModel featureModel, boolean ignoreAbstractFeatures) {
			super();
			this.featureModel = featureModel;
			this.featureSet = null;
			this.ignoreAbstractFeatures = ignoreAbstractFeatures;
		}
		
		@Override
		public void run() {
			if (featureSet != null) {
				buildNode = NodeCreator.createNodes(featureModel, featureSet).toCNF();
			} else {
				buildNode = NodeCreator.createNodes(featureModel, ignoreAbstractFeatures).toCNF();
			}
		}
	}

	public static int FEATURE_LIMIT_FOR_DEFAULT_COMPLETION = 150;

	private static final int TIMEOUT = 1000;

	private final ConfigurationPropagatorJobWrapper jobWrapper = new ConfigurationPropagatorJobWrapper(this);
	
	private Node rootNode = null, rootNodeWithoutHidden = null;
	private final Configuration configuration;

	/**
	 * This method creates a clone of the given {@link ConfigurationPropagator}
	 * @param configuration The configuration to clone
	 */
	ConfigurationPropagator(Configuration configuration) {
		this.configuration = configuration;
	}
	
	ConfigurationPropagator(ConfigurationPropagator propagator, Configuration configuration) {
		this.configuration = configuration;
		this.rootNode = propagator.rootNode.clone();
		this.rootNodeWithoutHidden = propagator.rootNodeWithoutHidden.clone();
	}
	
	ConfigurationPropagator(ConfigurationPropagator propagator) {
		this(propagator, propagator.configuration);
	}
	
	public ConfigurationPropagatorJobWrapper getJobWrapper() {
		return jobWrapper;
	}

	public void load(WorkMonitor workMonitor) {
		if (rootNode != null) {
			return;
		}
		final FeatureModel featureModel = configuration.getFeatureModel();
		if (featureModel.getRoot() != null) {
			// Build both cnfs simultaneously for better performance
			BuildThread buildThread1 = new BuildThread(featureModel, getRemoveFeatures(!configuration.ignoreAbstractFeatures, true));
			BuildThread buildThread2 = new BuildThread(featureModel, configuration.ignoreAbstractFeatures);
			
			buildThread1.start();
			buildThread2.start();
			
			try {
				buildThread2.join();
				buildThread1.join();
			} catch (InterruptedException e) {
				FMCorePlugin.getDefault().logError(e);
			}

			rootNodeWithoutHidden = buildThread1.buildNode;
			rootNode = buildThread2.buildNode;
		} else {
			rootNode = NodeCreator.createNodes(featureModel, configuration.ignoreAbstractFeatures).toCNF();
			rootNodeWithoutHidden = rootNode.clone();
		}
	}

	public LinkedList<List<String>> getSolutions(int max, WorkMonitor workMonitor) throws TimeoutException {
		if (rootNode == null) {
			return null;
		}
		final Node[] nodeArray = createNodeArray(createNodeList(), rootNode);
		return new SatSolver(new And(nodeArray), TIMEOUT).getSolutionFeatures(max);
	}
	
	/**
	 * Checks that all manual and automatic selections are valid.<br>
	 * Abstract features will <b>not</b> be ignored.
	 * @return  {@code true} if the current selection is a valid configuration
	 */
	public boolean isValid(WorkMonitor workMonitor) {
		if (rootNode == null) {
			return false;
		}
		final Node[] allFeatures = new Node[configuration.features.size() + 1];
		allFeatures[0] = rootNode.clone();
		int i = 1;
		for (SelectableFeature feature : configuration.features) {
			allFeatures[i++] = new Literal(feature.getFeature().getName(), feature.getSelection() == Selection.SELECTED);
		}
		try {
			return new SatSolver(new And(allFeatures), TIMEOUT).isSatisfiable();
		} catch (TimeoutException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return false;
	}
	
	/**
	 * Ignores hidden features.
	 * Use this, when propgate is disabled (hidden features are not updated).
	 */
	public boolean isValidNoHidden(WorkMonitor workMonitor) {
		if (rootNode == null) {
			return false;
		}
		final LinkedList<SelectableFeature> nonHiddenFeautres = new LinkedList<SelectableFeature>();

		for (SelectableFeature feature : configuration.features) {
			if (!feature.getFeature().hasHiddenParent()) {
				nonHiddenFeautres.add(feature);
			}
		}
		final Node[] allFeatures = new Node[nonHiddenFeautres.size() + 1];
		allFeatures[0] = rootNodeWithoutHidden.clone();
		int i = 1;
		for (SelectableFeature feature : nonHiddenFeautres) {
			allFeatures[i++] = new Literal(feature.getFeature().getName(), feature.getSelection() == Selection.SELECTED);
		}
		try {
			return new SatSolver(new And(allFeatures), TIMEOUT).isSatisfiable();
		} catch (TimeoutException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return false;
	}
	
	public boolean canBeValid(WorkMonitor workMonitor) {
		if (rootNode == null) {
			return false;
		}
		final List<Node> children = new ArrayList<Node>();
		
		for (SelectableFeature feature : configuration.features) {
			if (feature.getSelection() != Selection.UNDEFINED
					&& (configuration.ignoreAbstractFeatures || feature.getFeature().isConcrete())) {
				children.add(new Literal(feature.getFeature().getName(), feature.getSelection() == Selection.SELECTED));
			}
		}
		
		final Node[] allFeatures = new Node[children.size() + 1];
		children.toArray(allFeatures);
		allFeatures[children.size()] = rootNode.clone();
		
		try {
			return new SatSolver(new And(allFeatures), TIMEOUT).isSatisfiable();
		} catch (TimeoutException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return false;
	}
	
	public void leadToValidConfiguration(List<SelectableFeature> featureList, WorkMonitor workMonitor) {
		if (Preferences.defaultCompletion == Preferences.COMPLETION_ONE_CLICK && featureList.size() > FEATURE_LIMIT_FOR_DEFAULT_COMPLETION) {
			leadToValidConfiguration(featureList, Preferences.COMPLETION_OPEN_CLAUSES, workMonitor);
		} else {
			leadToValidConfiguration(featureList, Preferences.defaultCompletion, workMonitor);
		}
	}
	
	public void leadToValidConfiguration(List<SelectableFeature> featureList, int mode, WorkMonitor workMonitor) {
		for (SelectableFeature feature : configuration.features) {
			feature.setRecommended(Selection.UNDEFINED);
		}
		switch (mode) {
			case Preferences.COMPLETION_ONE_CLICK:
				leadToValidConfig1(featureList, workMonitor);
				break;
			case Preferences.COMPLETION_OPEN_CLAUSES:
				leadToValidConfig2(featureList, workMonitor);
				break;
			case Preferences.COMPLETION_NONE:
			default:
		}
	}
	
	private void leadToValidConfig1(List<SelectableFeature> featureList, WorkMonitor workMonitor) {
		if (rootNode == null) {
			return;
		}
		workMonitor.setMaxAbsoluteWork(featureList.size() + 1);
		final Map<String, Literal> featureMap = new HashMap<String, Literal>(configuration.features.size() << 1);
		final Map<String, Integer> featureToIndexMap = new HashMap<String, Integer>(featureList.size() << 1);
		
		for (SelectableFeature selectableFeature : configuration.features) {
			final Feature feature = selectableFeature.getFeature();
			if ((configuration.ignoreAbstractFeatures || feature.isConcrete()) && !feature.hasHiddenParent()) {
				final String featureName = feature.getName();
				featureMap.put(featureName,
					new Literal(featureName, selectableFeature.getSelection() == Selection.SELECTED));
			}
		}
		if (workMonitor.checkCancel()) {
			return;
		}

		final Literal[] literals = new Literal[featureList.size()];
		
		int i = 0;
		for (SelectableFeature feature : featureList) {
			final String featureName = feature.getFeature().getName();
			featureToIndexMap.put(featureName, i);
			literals[i++] = featureMap.remove(featureName);
		}
		
		final Node[] formula = new Node[featureMap.size() + 1];
		formula[0] = rootNodeWithoutHidden.clone();
		i = 1;
		for (Literal literal : featureMap.values()) {
			formula[i++] = literal;
		}
		
		final SatSolver solver = new SatSolver(new And(formula), TIMEOUT);
		
		final boolean[] changedLiterals = new boolean[literals.length];
		int j = 0;
		workMonitor.worked();
		for (SelectableFeature feature : featureList) {
			if (workMonitor.checkCancel()) {
				return;
			}
			final Literal l = literals[j++].clone();
			l.positive = !l.positive;
			
			final List<Literal> knownValues = solver.knownValues(l);
			
			for (Literal literal : knownValues) {
				Integer index = featureToIndexMap.get(literal.var);
				if (index != null) {
					final Literal knownL = literals[index];
					changedLiterals[index] = literal.positive != knownL.positive;
					knownL.positive = literal.positive;
				}
			}

			boolean result;
			try {
				result = solver.isSatisfiable(literals);
			} catch (TimeoutException e) {
				FMCorePlugin.getDefault().logError(e);
				result = false;
			}
			
			for (int k = 0; k < literals.length; k++) {
				final Literal knownL = literals[k];
				knownL.positive = changedLiterals[k] ^ knownL.positive;
				changedLiterals[k] = false;
			}
			
			if (result) {
				switch (feature.getManual()) {
				case SELECTED:
					feature.setRecommended(Selection.UNSELECTED); break;
				case UNSELECTED:
				case UNDEFINED:
					feature.setRecommended(Selection.SELECTED);
				}
			} else {
				feature.setRecommended(Selection.UNDEFINED);
			}
			
			workMonitor.invoke(feature);
			workMonitor.worked();
		}
	}
	
	private void leadToValidConfig2(List<SelectableFeature> featureList, WorkMonitor workMonitor) {
		final boolean[] results = new boolean[featureList.size()];
		if (rootNode == null) {
			return;
		}
		final Map<String, Boolean> featureMap = new HashMap<String, Boolean>(configuration.features.size() << 1);
		
		for (SelectableFeature selectableFeature : configuration.features) {
			final Feature feature = selectableFeature.getFeature();
			if ((configuration.ignoreAbstractFeatures || feature.isConcrete()) && !feature.hasHiddenParent()) {
				featureMap.put(feature.getName(), selectableFeature.getSelection() == Selection.SELECTED);
			}
		}
		for (SelectableFeature selectableFeature : featureList) {
			selectableFeature.setRecommended(Selection.UNSELECTED);
		}
		
		if (workMonitor.checkCancel()) {
			return;
		}
		
		final Node[] clauses = rootNodeWithoutHidden.getChildren();
		final HashMap<Object, Literal> literalMap = new HashMap<Object, Literal>();
		workMonitor.setMaxAbsoluteWork(clauses.length);
		for (int i = 0; i < clauses.length; i++) {
			if (workMonitor.checkCancel()) {
				return;
			}
			final Node clause = clauses[i];
			literalMap.clear();
			if (clause instanceof Literal) {
				final Literal literal = (Literal) clause;
				literalMap.put(literal.var, literal);
			} else {
				final Node[] orLiterals = clause.getChildren();
				for (int j = 0; j < orLiterals.length; j++) {
					final Literal literal = (Literal) orLiterals[j];
					literalMap.put(literal.var, literal);
				}
			}
			
			boolean satisfied = false;
			for (Literal literal : literalMap.values()) {
				Boolean selected = featureMap.get(literal.var);
				if (selected != null && selected == literal.positive) {
					satisfied = true;
					break;
				}
			}
			if (!satisfied) {
				int c = 0;
				for (SelectableFeature selectableFeature : featureList) {
					if (literalMap.containsKey(selectableFeature.getFeature().getName()) && !results[c]) {
						results[c] = true;
						
						switch (selectableFeature.getManual()) {
							case SELECTED:
								selectableFeature.setRecommended(Selection.UNSELECTED); break;
							case UNSELECTED:
							case UNDEFINED:
								selectableFeature.setRecommended(Selection.SELECTED);
						}
						
						workMonitor.invoke(selectableFeature);
					}
					c++;
				}
			}
			workMonitor.worked();
		}
	}
	
	/**
	 * Counts the number of possible solutions.
	 * @return a positive value equal to the number of solutions (if the method terminated in time)</br>
	 * 	or a negative value (if a timeout occurred) that indicates that there are more solutions than the absolute value
	 */
	public long number(long timeout, WorkMonitor workMonitor) {
		if (rootNode == null) {
			return 0;
		}
		final List<Node> children = new ArrayList<Node>();
		
		for (SelectableFeature feature : configuration.features) {
			if (feature.getSelection() != Selection.UNDEFINED 
					&& (configuration.ignoreAbstractFeatures || feature.getFeature().isConcrete())
					&& !feature.getFeature().hasHiddenParent()) {
				children.add(new Literal(feature.getFeature().getName(), feature.getSelection() == Selection.SELECTED));
			}
		}
		
		final Node[] nodeArray = createNodeArray(children, rootNodeWithoutHidden);
		return new SatSolver(new And(nodeArray), timeout).countSolutions();
	}
	
	private Node[] createNodeArray(List<Node> literals, Node ...formula) {
		final Node[] nodeArray = new Node[literals.size() + formula.length];
		literals.toArray(nodeArray);
		for (int i = 0; i < formula.length; i++) {
			nodeArray[literals.size() + i] = formula[i].clone();
		}
		return nodeArray;
	}

	private List<Node> createNodeList() {
		final List<Node> children = new ArrayList<Node>();
		
		for (SelectableFeature feature : configuration.features) {
			if (feature.getSelection() != Selection.UNDEFINED) {
				children.add(new Literal(feature.getFeature().getName(), feature.getSelection() == Selection.SELECTED));
			}
		}
		
		return children;
	}
	
	private Set<String> getRemoveFeatures(boolean abstractFeatures, boolean hiddenFeatures) {
		final Set<String> resultSet = new HashSet<String>();
		for (SelectableFeature selectableFeature : configuration.features) {
			final Feature f = selectableFeature.getFeature();
			if ((abstractFeatures && f.isAbstract()) || (hiddenFeatures && f.hasHiddenParent())) {
				resultSet.add(f.getName());
			}
		}
		return resultSet;
	}
	
	public void update(boolean redundantManual, String startFeatureName, WorkMonitor workMonitor) {
		if (rootNode == null) {
			return;
		}
		workMonitor.setMaxAbsoluteWork(configuration.features.size() + 1);
		
		configuration.resetAutomaticValues();
		
		final SatSolver manualSolver = new SatSolver(rootNode, ConfigurationPropagator.TIMEOUT);
		
		final List<Node> manualSelected = (redundantManual) ? new LinkedList<Node>() : new ArrayList<Node>();
		for (SelectableFeature feature : configuration.features) {
			switch (feature.getManual()) {
				case SELECTED: manualSelected.add(new Literal(feature.getFeature().getName(), true)); break;
				case UNSELECTED: manualSelected.add(new Literal(feature.getFeature().getName(), false)); break;
				default:
			}
		}
		
		workMonitor.worked();
		
		final HashMap<SelectableFeature, Selection> possibleRedundantManual = new HashMap<SelectableFeature, Selection>();
		
		if (redundantManual) {
			for (Iterator<Node> iterator = manualSelected.iterator(); iterator.hasNext();) {
				final Literal l = (Literal) iterator.next();
				try {
					l.positive = !l.positive;
					if (!manualSolver.isSatisfiable(manualSelected)) {
						final SelectableFeature feature = configuration.table.get(l.var);
						possibleRedundantManual.put(feature, feature.getManual());
						feature.setManual(Selection.UNDEFINED);
						iterator.remove();
					}
				} catch (TimeoutException e) {
					FMCorePlugin.getDefault().logError(e);
				} finally {
					l.positive = !l.positive;
				}
			}
		}
		
		final Node[] nodeArray = createNodeArray(manualSelected, rootNode);
		final SatSolver automaticSolver = new SatSolver(new And(nodeArray), ConfigurationPropagator.TIMEOUT);
		
		ListIterator<SelectableFeature> it = configuration.features.listIterator();
		int index = -1;
		if (startFeatureName != null) {
			while (it.hasNext()) {
				final SelectableFeature feature = it.next();
				
				if (startFeatureName.equals(feature.getFeature().getName())) {
					it.previous();
					index = it.nextIndex();
					break;
				}
			}
		}
		
		if (index > 0) {
			updateAllFeatures(automaticSolver, it, workMonitor, manualSelected, manualSolver, possibleRedundantManual);
			updateAllFeatures(automaticSolver, configuration.features.subList(0, index).iterator(), workMonitor, manualSelected, manualSolver, possibleRedundantManual);
		} else {
			updateAllFeatures(automaticSolver, configuration.features.iterator(), workMonitor, manualSelected, manualSolver, possibleRedundantManual);
		}
	}

	private void updateAllFeatures(final SatSolver automaticSolver, Iterator<SelectableFeature> it, WorkMonitor workMonitor, List<Node> manualSelected, SatSolver manualSolver, HashMap<SelectableFeature, Selection> possibleRedundantManual) {
		final Node[] manualSelectedArray = createNodeArray(manualSelected);
		int i = 0;
		while (it.hasNext()) {
			final SelectableFeature feature = it.next();
			if (feature.getManual() == Selection.UNDEFINED) {
				Literal l = new Literal(feature.getFeature().getName(), true);
				try {
					if (!automaticSolver.isSatisfiable(l)) {
						feature.setAutomatic(Selection.UNSELECTED);
					} else {
						l = new Literal(feature.getFeature().getName(), false);
						if (!automaticSolver.isSatisfiable(l)) {
							feature.setAutomatic(Selection.SELECTED);
						} else {
							feature.setAutomatic(Selection.UNDEFINED);
							Selection manualSelection = possibleRedundantManual.get(feature);
							if (manualSelection != null) {
								feature.setManual(manualSelection);
							}
						}
					}
				} catch (TimeoutException e) {
					FMCorePlugin.getDefault().logError(e);
				}
			} else {
				Literal l = (Literal) manualSelectedArray[i++];
				while (!feature.getFeature().getName().equals(l.var)) {
					l = (Literal) manualSelectedArray[i++];
				}
				try {
					l.positive = !l.positive;
					if (!manualSolver.isSatisfiable(manualSelectedArray)) {
						feature.setAutomatic(l.positive ? Selection.UNSELECTED : Selection.SELECTED);
					}
				} catch (TimeoutException e) {
					FMCorePlugin.getDefault().logError(e);
				} finally {
					l.positive = !l.positive;
				}
			}
			workMonitor.invoke(feature);
			workMonitor.worked();
		}
	}
	
	ConfigurationPropagator clone(Configuration configuration) {
		return new ConfigurationPropagator(this, configuration);
	}
	
}
