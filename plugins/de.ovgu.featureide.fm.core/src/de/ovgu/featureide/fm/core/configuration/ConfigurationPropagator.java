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
	private boolean propagate = true;

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
		this.propagate = propagator.propagate;
	}
	
	ConfigurationPropagator(ConfigurationPropagator propagator) {
		this(propagator, propagator.configuration);
	}
	
	public ConfigurationPropagatorJobWrapper getJobWrapper() {
		return jobWrapper;
	}
	
	public boolean isPropagate() {
		return propagate;
	}

	public void setPropagate(boolean propagate) {
		this.propagate = propagate;
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
	
	public boolean canBeValid(WorkMonitor workMonitor) {
		if (rootNode == null) {
			return false;
		}
		final List<Node> children = new ArrayList<Node>();
		
		for (SelectableFeature feature : configuration.features) {
			if (feature.getSelection() != Selection.UNDEFINED) {
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
	
//	public ValidConfigJob leadToValidConfiguration(List<SelectableFeature> featureList, WorkMonitor workMonitor) {
//		if (Preferences.defaultCompletion == Preferences.COMPLETION_ONE_CLICK && featureList.size() > FEATURE_LIMIT_FOR_DEFAULT_COMPLETION) {
//			return leadToValidConfiguration(featureList, Preferences.COMPLETION_OPEN_CLAUSES);
//		}
//		return leadToValidConfiguration(featureList, Preferences.defaultCompletion);
//	}
//	
//	public ValidConfigJob leadToValidConfiguration(List<SelectableFeature> featureList, int mode, WorkMonitor workMonitor) {
//		switch (mode) {
//			case Preferences.COMPLETION_ONE_CLICK:
//				return new ValidConfigJob1(featureList);
//			case Preferences.COMPLETION_OPEN_CLAUSES:
//				return new ValidConfigJob2(featureList);
//			case Preferences.COMPLETION_NONE:
//			default:
//				return null;
//		}
//	}
	
	public boolean[] leadToValidConfiguration(List<SelectableFeature> featureList, WorkMonitor workMonitor) {
		if (Preferences.defaultCompletion == Preferences.COMPLETION_ONE_CLICK && featureList.size() > FEATURE_LIMIT_FOR_DEFAULT_COMPLETION) {
			return leadToValidConfiguration(featureList, Preferences.COMPLETION_OPEN_CLAUSES, workMonitor);
		}
		return leadToValidConfiguration(featureList, Preferences.defaultCompletion, workMonitor);
	}
	
	public boolean[] leadToValidConfiguration(List<SelectableFeature> featureList, int mode, WorkMonitor workMonitor) {
		switch (mode) {
			case Preferences.COMPLETION_ONE_CLICK:
				return leadToValidConfig1(featureList, workMonitor);
			case Preferences.COMPLETION_OPEN_CLAUSES:
				return leadToValidConfig2(featureList, workMonitor);
			case Preferences.COMPLETION_NONE:
			default:
				return null;
		}
	}
	
//	public abstract class ValidConfigJob extends AStoppableJob {
//		protected final boolean[] results;
//		protected final List<SelectableFeature> featureList;
//		
//		public ValidConfigJob(List<SelectableFeature> featureList) {
//			super("Configuration coloring");
//			results = new boolean[featureList.size()];
//			this.featureList = featureList;
//		}
//		
//		public boolean[] getResults() {
//			return results;
//		}
//	}
	
	private boolean[] leadToValidConfig1(List<SelectableFeature> featureList, WorkMonitor workMonitor) {
		final boolean[] results = new boolean[featureList.size()];
		if (rootNode == null) {
			return results;
		}
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
			return results;
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
		
		for (int j = 0; j < literals.length; j++) {
			if (workMonitor.checkCancel()) {
				return results;
			}
			final Literal l = literals[j].clone();
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
			
			try {
				results[j] = solver.isSatisfiable(literals);
			} catch (TimeoutException e) {
				FMCorePlugin.getDefault().logError(e);
				results[j] = false;
			}
			
			for (int k = 0; k < literals.length; k++) {
				final Literal knownL = literals[k];
				knownL.positive = changedLiterals[k] ^ knownL.positive;
				changedLiterals[k] = false;
			}
		}

		return results;
	}
	
	private boolean[] leadToValidConfig2(List<SelectableFeature> featureList, WorkMonitor workMonitor) {
		final boolean[] results = new boolean[featureList.size()];
		if (rootNode == null) {
			return results;
		}
		final Map<String, Boolean> featureMap = new HashMap<String, Boolean>(configuration.features.size() << 1);
		
		for (SelectableFeature selectableFeature : configuration.features) {
			final Feature feature = selectableFeature.getFeature();
			if ((configuration.ignoreAbstractFeatures || feature.isConcrete()) && !feature.hasHiddenParent()) {
				featureMap.put(feature.getName(), selectableFeature.getSelection() == Selection.SELECTED);
			}
		}
		if (workMonitor.checkCancel()) {
			return results;
		}
		
		final Node[] clauses = rootNodeWithoutHidden.getChildren();
		final HashMap<Object, Literal> literalMap = new HashMap<Object, Literal>();
		for (int i = 0; i < clauses.length; i++) {
			if (workMonitor.checkCancel()) {
				return results;
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
					if (literalMap.containsKey(selectableFeature.getFeature().getName())) {
						results[c] = true;
					}
					c++;
				}
			}
		}
		
		return results;
	}
	
	
//	/**
//	 * Convenience method.
//	 * @return the values of number(250)
//	 * @see #number(long)
//	 */
//	public long number() {
//		return number(250);
//	}
	
	/**
	 * Counts the number of possible solutions.
	 * @return a positive value equal to the number of solutions (if the method terminated in time)</br>
	 * 	or a negative value (if a timeout occured) that indicates that there are more solutions than the absolute value
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
	
	public void update(boolean manual, boolean redundantManual, String startFeatureName, WorkMonitor workMonitor) {
		if (!propagate || rootNode == null) {
			return;
		}
		workMonitor.setMaxAbsoluteWork(configuration.features.size() + 1);
		
		configuration.resetAutomaticValues();
		
		final SatSolver manualSolver = (manual || redundantManual) ? new SatSolver(rootNode, ConfigurationPropagator.TIMEOUT) : null;
		
		List<Node> manualSelected = new ArrayList<Node>();
		for (SelectableFeature feature : configuration.features) {
			switch (feature.getManual()) {
				case SELECTED: manualSelected.add(new Literal(feature.getFeature().getName(), true)); break;
				case UNSELECTED: manualSelected.add(new Literal(feature.getFeature().getName(), false)); break;
				default:
			}
		}
		
		workMonitor.worked();
		
		if (redundantManual) {
			updateManualFeatures(manualSolver, manualSelected, workMonitor);

			manualSelected = new ArrayList<Node>();
			for (SelectableFeature feature : configuration.features) {
				switch (feature.getManual()) {
					case SELECTED: manualSelected.add(new Literal(feature.getFeature().getName(), true)); break;
					case UNSELECTED: manualSelected.add(new Literal(feature.getFeature().getName(), false)); break;
					default:
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
		
		if (index > -1) {
			updateAllFeatures(automaticSolver, it, workMonitor);
			updateAllFeatures(automaticSolver, configuration.features.subList(0, index).iterator(), workMonitor);
		} else {
			updateAllFeatures(automaticSolver, configuration.features.iterator(), workMonitor);
		}
		
		if (manual) {
			updateManualFeatures(manualSolver, manualSelected, workMonitor);
		}
	}

	private void updateManualFeatures(final SatSolver manualSolver, List<Node> manualSelected, WorkMonitor workMonitor) {
		final Node[] manualSelectedArray = createNodeArray(manualSelected);
		for (int i = 0; i < manualSelectedArray.length; i++) {
			Literal l = (Literal) manualSelectedArray[i];
			try {
				l.positive = !l.positive;
				if (!manualSolver.isSatisfiable(manualSelectedArray)) {
					SelectableFeature feature = configuration.table.get(l.var);
					feature.setManual(Selection.UNDEFINED);
				}
				l.positive = !l.positive;
			} catch (TimeoutException e) {
				e.printStackTrace();
			}
			workMonitor.invoke(null);
		}
	}

	private void updateAllFeatures(final SatSolver automaticSolver, Iterator<SelectableFeature> it, WorkMonitor workMonitor) {
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
						}
					}
				} catch (TimeoutException e) {
					e.printStackTrace();
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
