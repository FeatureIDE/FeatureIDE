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

import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.osgi.service.prefs.BackingStoreException;
import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

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

	public static final int 
		COMPLETION_NONE = 0,
		COMPLETION_ONE_CLICK = 1,
		COMPLETION_OPEN_CLAUSES = 2;

	public static int FEATURE_LIMIT_FOR_DEFAULT_COMPLETION = 150;
	private static int defaultCompletion;
	static {
		final IEclipsePreferences preferences = InstanceScope.INSTANCE.getNode("de.ovgu.featureide.fm.core");
		final String pref = preferences.get("configCompletion", Integer.toString(COMPLETION_ONE_CLICK));
		try {
			defaultCompletion = Integer.parseInt(pref);
		} catch (Exception e) {
			defaultCompletion = COMPLETION_ONE_CLICK;
		}
	}

	private static final int TIMEOUT = 1000;

	private final SelectableFeature root;

	private final ArrayList<SelectableFeature> features = new ArrayList<SelectableFeature>();

	private final Hashtable<String, SelectableFeature> table = new Hashtable<String, SelectableFeature>();

	private final Node rootNode, rootNodeWithoutHidden;

	private final FeatureModel featureModel;

	private final boolean ignoreAbstractFeatures;
	private boolean propagate;
	
	public static int getDefaultCompletion() {
		return defaultCompletion;
	}
	
	public static void setDefaultCompletion(int defaultCompletion) {
		Configuration.defaultCompletion = defaultCompletion;
		final IEclipsePreferences preferences = InstanceScope.INSTANCE.getNode("de.ovgu.featureide.fm.core");
		preferences.put("configCompletion", Integer.toString(defaultCompletion));
		try {
			preferences.flush();
		} catch (BackingStoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * This method creates a clone of the given {@link Configuration}
	 * @param configuration The configuration to clone
	 */
	public Configuration(Configuration configuration) {
		this(configuration, configuration.featureModel, configuration.propagate);
	}

	public Configuration(Configuration configuration, FeatureModel featureModel, boolean propagate) {
		this.featureModel = featureModel;
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
		this.propagate = propagate;
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
		initFeatures(root, featureRoot);
		
		// Build both cnfs simultaneously for better performance
		if (featureRoot != null) {
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
			rootNode = NodeCreator.createNodes(featureModel, ignoreAbstractFeatures).toCNF();
			rootNodeWithoutHidden = rootNode.clone();
		}
		
		updateAutomaticValues();
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
	
	public boolean[] leadToValidConfiguration(List<SelectableFeature> featureList) {
		if (defaultCompletion == COMPLETION_NONE) {
			return leadToValidConfiguration(featureList, defaultCompletion);
		} else if (featureList.size() > FEATURE_LIMIT_FOR_DEFAULT_COMPLETION) {
			return leadToValidConfiguration(featureList, COMPLETION_OPEN_CLAUSES);
		}
		return leadToValidConfiguration(featureList, defaultCompletion);
	}
	
	public boolean[] leadToValidConfiguration(List<SelectableFeature> featureList, int mode) {
		switch (mode) {
			case COMPLETION_ONE_CLICK:
				return leadsToValidConfiguration1(featureList);
			case COMPLETION_OPEN_CLAUSES:
				return leadsToValidConfiguration3(featureList);
			case COMPLETION_NONE:
			default:
				return new boolean[featureList.size()];
		}
	}
	
	private boolean[] leadsToValidConfiguration1(List<SelectableFeature> featureList) {
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

		final boolean[] results = new boolean[literals.length];
		final boolean[] changedLiterals = new boolean[literals.length];
		
		for (int j = 0; j < literals.length; j++) {
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
	
	private boolean[] leadsToValidConfiguration3(List<SelectableFeature> featureList) {
		final Map<String, Boolean> featureMap = new HashMap<String, Boolean>(features.size() << 1);
		
		for (SelectableFeature selectableFeature : features) {
			final Feature feature = selectableFeature.getFeature();
			if ((ignoreAbstractFeatures || feature.isConcrete()) && !feature.hasHiddenParent()) {
				featureMap.put(feature.getName(), selectableFeature.getSelection() == Selection.SELECTED);
			}
		}
		
		final boolean[] results = new boolean[featureList.size()];
		
		final Node[] clauses = rootNodeWithoutHidden.getChildren();
		final HashMap<Object, Literal> literalMap = new HashMap<Object, Literal>();
		for (int i = 0; i < clauses.length; i++) {
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
	
	public long number() {
		return number(250);
	}
	
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
		}
		updateAutomaticValues();
	}
	
	public void setAutomatic(SelectableFeature feature, Selection selection) {
		feature.setAutomatic(selection);
		updateAutomaticValues();
	}
	
	public void setAutomatic(String name, Selection selection) {
		SelectableFeature feature = table.get(name);
		if (feature == null) {
			throw new FeatureNotFoundException();
		}
		setAutomatic(feature, selection);
	}

	public void setManual(SelectableFeature feature, Selection selection) {
		feature.setManual(selection);
		updateAutomaticValues();
	}

	public void setManual(String name, Selection selection) {
		SelectableFeature feature = table.get(name);
		if (feature == null) {
			throw new FeatureNotFoundException();
		}
		setManual(feature, selection);
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
	
	private void updateAutomaticValues() {
		if (!propagate)
			return;
		resetAutomaticValues();
		
		Node[] nodeArray = createNodeArray(createNodeList(), rootNode);
		final SatSolver solver = new SatSolver(new And(nodeArray), TIMEOUT);
		for (Literal literal : solver.knownValues()) {
			SelectableFeature feature = table.get(literal.var);
			if (feature != null) {
				if (feature.getManual() == Selection.UNDEFINED) {
					feature.setAutomatic(literal.positive ? Selection.SELECTED : Selection.UNSELECTED);
				}
			}
		}
		
		final List<Node> children = new ArrayList<Node>();
		boolean calculateHiddenFeatures = false;
		
		for (SelectableFeature feature : features) {
			if (feature.getFeature().hasHiddenParent()) {
				calculateHiddenFeatures = true;
			} else {
				children.add(new Literal(feature.getFeature().getName(), feature.getSelection() == Selection.SELECTED));
			}
		}
		
		if (calculateHiddenFeatures) {
			nodeArray = createNodeArray(children, rootNode);
			final SatSolver hiddenSolver = new SatSolver(new And(nodeArray), TIMEOUT);
			for (Literal literal : hiddenSolver.knownValues()) {
				SelectableFeature feature = table.get(literal.var);
				if (feature != null) {
					if (feature.getManual() == Selection.UNDEFINED && feature.getFeature().hasHiddenParent()) {
						feature.setAutomatic(literal.positive ? Selection.SELECTED : Selection.UNSELECTED);
					}
				}
			}
		}
	}
}
