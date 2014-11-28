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
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.List;
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
import de.ovgu.featureide.fm.core.job.AStoppableJob;

/**
 * Represents a configuration and provides operations for the configuration process.
 */
public class Configuration {
	
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

	private final SelectableFeature root;

	private final ArrayList<SelectableFeature> features = new ArrayList<SelectableFeature>();

	private final Hashtable<String, SelectableFeature> table = new Hashtable<String, SelectableFeature>();

	private final Node rootNode, rootNodeWithoutHidden;

	private final FeatureModel featureModel;

	private final boolean ignoreAbstractFeatures;
	private boolean propagate;

	/**
	 * This method creates a clone of the given {@link Configuration}
	 * @param configuration The configuration to clone
	 */
	public Configuration(Configuration configuration) {
		this.featureModel = configuration.featureModel;
		this.propagate = false;
		this.ignoreAbstractFeatures = configuration.ignoreAbstractFeatures;

		Feature featureRoot = featureModel.getRoot();
		root = new SelectableFeature(this, featureRoot);
		initFeatures(root, featureRoot);
		
		rootNode = configuration.rootNode.clone();
		rootNodeWithoutHidden = configuration.rootNodeWithoutHidden.clone();
		
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
		this.propagate = false;
		this.ignoreAbstractFeatures = configuration.ignoreAbstractFeatures;
		
		Feature featureRoot = featureModel.getRoot();
		root = new SelectableFeature(this, featureRoot);
		
		if (featureRoot != null) {
			initFeatures(root, featureRoot);

			// Build both cnfs simultaneously for better performance
			BuildThread buildThread1 = new BuildThread(featureModel, getRemoveFeatures(!ignoreAbstractFeatures, true));
			BuildThread buildThread2 = new BuildThread(featureModel, ignoreAbstractFeatures);
			
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
			features.add(root);
			table.put(root.getName(), root);
			rootNode = NodeCreator.createNodes(featureModel, ignoreAbstractFeatures).toCNF();
			rootNodeWithoutHidden = rootNode.clone();
		}
		
		for (SelectableFeature f : configuration.features) {
			try {
				setManual(f.getName(), (f.getManual()));
			} catch (FeatureNotFoundException e) {
			}
		}
		
		this.propagate = configuration.propagate;
		update(true);
	}
	
	public Configuration(FeatureModel featureModel) {
		this(featureModel, true);
	}
	
	public Configuration(FeatureModel featureModel, boolean propagate) {
		this(featureModel, propagate, true);
	}
	
	public Configuration(final FeatureModel featureModel, boolean propagate, final boolean ignoreAbstractFeatures) {
		this.featureModel = featureModel;
		this.propagate = propagate;
		this.ignoreAbstractFeatures = ignoreAbstractFeatures;

		Feature featureRoot = featureModel.getRoot();
		root = new SelectableFeature(this, featureRoot);
		
		if (featureRoot != null) {
			initFeatures(root, featureRoot);

			// Build both cnfs simultaneously for better performance
			BuildThread buildThread1 = new BuildThread(featureModel, getRemoveFeatures(!ignoreAbstractFeatures, true));
			BuildThread buildThread2 = new BuildThread(featureModel, ignoreAbstractFeatures);
			
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
			features.add(root);
			table.put(root.getName(), root);
			rootNode = NodeCreator.createNodes(featureModel, ignoreAbstractFeatures).toCNF();
			rootNodeWithoutHidden = rootNode.clone();
		}
		
		update(true);
	}

	public FeatureModel getFeatureModel() {
		return featureModel;
	}

	public List<SelectableFeature> getFeatures() {
		return Collections.unmodifiableList(features);
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
				result.add(feature.getFeature().getName());
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
	
	public List<SelectableFeature> getManualFeatures() {
		final List<SelectableFeature> featureList = new LinkedList<SelectableFeature>();
		for (SelectableFeature selectableFeature : features) {
			if (selectableFeature.getAutomatic() == Selection.UNDEFINED && !selectableFeature.getFeature().hasHiddenParent()) {
				featureList.add(selectableFeature);
			}
		}
		return featureList;
	}

	public LinkedList<List<String>> getSolutions(int max) throws TimeoutException {
		final Node[] nodeArray = createNodeArray(createNodeList(), rootNode);
		return new SatSolver(new And(nodeArray), TIMEOUT).getSolutionFeatures(max);
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
	
	/**
	 * Checks that all manual and automatic selections are valid.<br>
	 * Abstract features will <b>not</b> be ignored.
	 * @return  {@code true} if the current selection is a valid configuration
	 */
	public boolean isValid() {
		final Node[] allFeatures = new Node[features.size() + 1];
		allFeatures[0] = rootNode.clone();
		int i = 1;
		for (SelectableFeature feature : features) {
			allFeatures[i++] = new Literal(feature.getFeature().getName(), feature.getSelection() == Selection.SELECTED);
		}
		try {
			return new SatSolver(new And(allFeatures), TIMEOUT).isSatisfiable();
		} catch (TimeoutException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return false;
	}
	
	public boolean canBeValid() {
		final List<Node> children = new ArrayList<Node>();
		
		for (SelectableFeature feature : features) {
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
	
	public ValidConfigJob leadToValidConfiguration(List<SelectableFeature> featureList) {
		if (Preferences.defaultCompletion == Preferences.COMPLETION_ONE_CLICK && featureList.size() > FEATURE_LIMIT_FOR_DEFAULT_COMPLETION) {
			return leadToValidConfiguration(featureList, Preferences.COMPLETION_OPEN_CLAUSES);
		}
		return leadToValidConfiguration(featureList, Preferences.defaultCompletion);
	}
	
	public ValidConfigJob leadToValidConfiguration(List<SelectableFeature> featureList, int mode) {
		switch (mode) {
			case Preferences.COMPLETION_ONE_CLICK:
				return new ValidConfigJob1(featureList);
			case Preferences.COMPLETION_OPEN_CLAUSES:
				return new ValidConfigJob2(featureList);
			case Preferences.COMPLETION_NONE:
			default:
				return null;
		}
	}
	
	public abstract class ValidConfigJob extends AStoppableJob {
		protected final boolean[] results;
		protected final List<SelectableFeature> featureList;
		
		public ValidConfigJob(List<SelectableFeature> featureList) {
			super("Configuration coloring");
			results = new boolean[featureList.size()];
			this.featureList = featureList;
		}
		
		public boolean[] getResults() {
			return results;
		}
	}
	
	private class ValidConfigJob1 extends ValidConfigJob {
		public ValidConfigJob1(List<SelectableFeature> featureList) {
			super(featureList);
		}
		
		@Override
		protected boolean work() {
			final Map<String, Literal> featureMap = new HashMap<String, Literal>(features.size() << 1);
			final Map<String, Integer> featureToIndexMap = new HashMap<String, Integer>(featureList.size() << 1);
			
			for (SelectableFeature selectableFeature : features) {
				final Feature feature = selectableFeature.getFeature();
				if ((ignoreAbstractFeatures || feature.isConcrete()) && !feature.hasHiddenParent()) {
					final String featureName = feature.getName();
					featureMap.put(featureName,
						new Literal(featureName, selectableFeature.getSelection() == Selection.SELECTED));
				}
			}
			if (checkCancel()) {
				return false;
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
				if (checkCancel()) {
					return false;
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

			return true;
		}
	}
	
	
	private class ValidConfigJob2 extends ValidConfigJob {
		public ValidConfigJob2(List<SelectableFeature> featureList) {
			super(featureList);
		}
		
		@Override
		protected boolean work() {
			final Map<String, Boolean> featureMap = new HashMap<String, Boolean>(features.size() << 1);
			
			for (SelectableFeature selectableFeature : features) {
				final Feature feature = selectableFeature.getFeature();
				if ((ignoreAbstractFeatures || feature.isConcrete()) && !feature.hasHiddenParent()) {
					featureMap.put(feature.getName(), selectableFeature.getSelection() == Selection.SELECTED);
				}
			}
			if (checkCancel()) {
				return false;
			}
			
			final Node[] clauses = rootNodeWithoutHidden.getChildren();
			final HashMap<Object, Literal> literalMap = new HashMap<Object, Literal>();
			for (int i = 0; i < clauses.length; i++) {
				if (checkCancel()) {
					return false;
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
			
			return true;
		}
	}
	
	
	/**
	 * Convenience method.
	 * @return the values of number(250)
	 * @see #number(long)
	 */
	public long number() {
		return number(250);
	}
	
	/**
	 * Counts the number of possible solutions.
	 * @return a positive value equal to the number of solutions (if the method terminated in time)</br>
	 * 	or a negative value (if a timeout occured) that indicates that there are more solutions than the absolute value
	 */
	public long number(long timeout) {
		final List<Node> children = new ArrayList<Node>();
		
		for (SelectableFeature feature : features) {
			if (feature.getSelection() != Selection.UNDEFINED 
					&& (ignoreAbstractFeatures || feature.getFeature().isConcrete())
					&& !feature.getFeature().hasHiddenParent()) {
				children.add(new Literal(feature.getFeature().getName(), feature.getSelection() == Selection.SELECTED));
			}
		}
		
		final Node[] nodeArray = createNodeArray(children, rootNodeWithoutHidden);
		return new SatSolver(new And(nodeArray), timeout).countSolutions();
	}

	public void resetValues() {
		for (SelectableFeature feature : features) {
			feature.setManual(Selection.UNDEFINED);
			feature.setAutomatic(Selection.UNDEFINED);
		}
		update();
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

	public void setManual(SelectableFeature feature, Selection selection) {
		feature.setManual(selection);
		update(true);
	}

	public void setManual(String name, Selection selection) {
		SelectableFeature feature = table.get(name);
		if (feature == null) {
			throw new FeatureNotFoundException();
		}
		setManual(feature, selection);
	}
	
	public boolean isPropagate() {
		return propagate;
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
		
		for (SelectableFeature feature : features) {
			if (feature.getSelection() != Selection.UNDEFINED) {
				children.add(new Literal(feature.getFeature().getName(), feature.getSelection() == Selection.SELECTED));
			}
		}
		
		return children;
	}
	
	private Set<String> getRemoveFeatures(boolean abstractFeatures, boolean hiddenFeatures) {
		final Set<String> resultSet = new HashSet<String>();
		for (SelectableFeature selectableFeature : features) {
			final Feature f = selectableFeature.getFeature();
			if ((abstractFeatures && f.isAbstract()) || (hiddenFeatures && f.hasHiddenParent())) {
				resultSet.add(f.getName());
			}
		}
		return resultSet;
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
	
	private void resetAutomaticValues() {
		for (SelectableFeature feature : features) {
			feature.setAutomatic(Selection.UNDEFINED);
		}
	}
	
	/**
	 * Turns all automatic into manual values
	 * @param discardDeselected if {@code true} all automatic deselected features get undefined instead of manual deselected
	 */
	public void makeManual(boolean discardDeselected) {
		if (propagate) {
			return;
		}
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
	
	public void update() {
		update(false, false);
	}
	
	public void update(boolean manual) {
		update(manual, false);
	}
	
	public void update(boolean manual, boolean redundantManual) {
		if (!propagate) {
			return;
		}
		resetAutomaticValues();
		
		final SatSolver manualSolver = (manual || redundantManual) ? new SatSolver(rootNode, TIMEOUT) : null;
		
		List<Node> manualSelected = new ArrayList<Node>();
		for (SelectableFeature feature : features) {
			switch (feature.getManual()) {
				case SELECTED: manualSelected.add(new Literal(feature.getFeature().getName(), true)); break;
				case UNSELECTED: manualSelected.add(new Literal(feature.getFeature().getName(), false)); break;
				default:
			}
		}
		
		if (redundantManual) {
			final Node[] manualSelectedArray = createNodeArray(manualSelected);
			for (int i = 0; i < manualSelectedArray.length; i++) {
				Literal l = (Literal) manualSelectedArray[i];
				try {
					l.positive = !l.positive;
					if (!manualSolver.isSatisfiable(manualSelectedArray)) {
						SelectableFeature feature = table.get(l.var);
						feature.setManual(Selection.UNDEFINED);
					}
					l.positive = !l.positive;
				} catch (TimeoutException e) {
					e.printStackTrace();
				}
			}

			manualSelected = new ArrayList<Node>();
			for (SelectableFeature feature : features) {
				switch (feature.getManual()) {
					case SELECTED: manualSelected.add(new Literal(feature.getFeature().getName(), true)); break;
					case UNSELECTED: manualSelected.add(new Literal(feature.getFeature().getName(), false)); break;
					default:
				}
			}
		}
		
		final Node[] nodeArray = createNodeArray(manualSelected, rootNode);
		final SatSolver automaticSolver = new SatSolver(new And(nodeArray), TIMEOUT);
		
		for (SelectableFeature feature : features) {
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
		}
		
		
		if (manual) {
			final Node[] manualSelectedArray = createNodeArray(manualSelected);
			for (int i = 0; i < manualSelectedArray.length; i++) {
				Literal l = (Literal) manualSelectedArray[i];
				try {
					l.positive = !l.positive;
					if (!manualSolver.isSatisfiable(manualSelectedArray)) {
						SelectableFeature feature = table.get(l.var);
						feature.setManual(Selection.UNDEFINED);
					}
					l.positive = !l.positive;
				} catch (TimeoutException e) {
					e.printStackTrace();
				}
			}
		}
	}
	
}
