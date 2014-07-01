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
import java.util.Map.Entry;
import java.util.Set;

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

	private static final int TIMEOUT = 1000;

	private final SelectableFeature root;

	private final ArrayList<SelectableFeature> features = new ArrayList<SelectableFeature>();

	private final Hashtable<String, SelectableFeature> table = new Hashtable<String, SelectableFeature>();

	private final Node rootNode;
	private final Node rootNodeWithoutHidden;

	private final FeatureModel featureModel;

	private boolean propagate;

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
	
	public Configuration(FeatureModel featureModel, boolean propagate, boolean ignoreAbstractFeatures) {
		this.featureModel = featureModel;
		this.propagate = propagate;

		Feature featureRoot = featureModel.getRoot();
		root = new SelectableFeature(this, featureRoot);
		initFeatures(root, featureRoot);

		rootNode = NodeCreator.createNodes(featureModel, ignoreAbstractFeatures).toCNF();
		rootNodeWithoutHidden = NodeCreator.createNodes(featureModel, getRemoveFeatures(!ignoreAbstractFeatures, true)).toCNF();
		
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
		final Map<String, Boolean> featureMap = new HashMap<String, Boolean>(features.size() << 1);
		for (SelectableFeature feature : features) {
			featureMap.put(feature.getFeature().getName(), feature.getSelection() == Selection.SELECTED);
		}

		final Map<String, Integer> featureMap2 = new HashMap<String, Integer>(featureList.size() << 1);
		final boolean[] results = new boolean[featureList.size()];
		final Node[] literals = new Node[featureList.size()];
		int i = 0;
		for (SelectableFeature feature : featureList) {
			featureMap.remove(feature.getFeature().getName());
			featureMap2.put(feature.getFeature().getName(), i);
			literals[i++] = new Literal(feature.getFeature().getName(), feature.getSelection() == Selection.SELECTED);
		}
		
		final Node[] formula = new Node[featureMap.size() + 2];
		formula[0] = rootNode.clone();
		i = 1;
		for (Entry<String, Boolean> feature : featureMap.entrySet()) {
			formula[i++] = new Literal(feature.getKey(), feature.getValue());
		}
		
		for (int j = 0; j < literals.length; j++) {
			final Node[] newLiterals = new Node[featureList.size()];
			for (int k = 0; k < newLiterals.length; k++) {
				Literal l = (Literal) literals[k];
				newLiterals[k] = new Literal(l.var, l.positive);
			}
			final Literal l = (Literal) newLiterals[j];
			l.positive = !l.positive;
			formula[formula.length - 1] = l;
			final SatSolver solver = new SatSolver(new And(formula), TIMEOUT);
			
			for (Literal literal : solver.knownValues()) {
				Integer index = featureMap2.get(literal.var);
				if (index != null) {
					newLiterals[index] = literal;
				}
			}
			
			try {
				results[j] = solver.isSatisfiable(newLiterals);
			} catch (TimeoutException e) {
				FMCorePlugin.getDefault().logError(e);
				results[j] = false;
			}
		}

		return results;
	}

	public boolean[] leadToValidConfiguration2(List<SelectableFeature> featureList) {
		final Map<String, Boolean> featureMap = new HashMap<String, Boolean>(features.size() << 1);
		for (SelectableFeature feature : features) {
			if (feature.getSelection() != Selection.UNDEFINED) {
				featureMap.put(feature.getFeature().getName(), feature.getSelection() == Selection.SELECTED);
			}
		}

		// manual set features
		final boolean[] results = new boolean[featureList.size()];
		final Node[] literals = new Node[featureList.size()];
		int i = 0;
		for (SelectableFeature feature : featureList) {
			featureMap.remove(feature.getName());
			literals[i++] = new Literal(feature.getFeature().getName(), feature.getSelection() == Selection.SELECTED);
		}

		// automatic set features
		final Node[] formula = new Node[featureMap.size()  + 1];
		formula[0] = rootNode.clone();
		i = 1;
		for (Entry<String, Boolean> feature : featureMap.entrySet()) {
			formula[i++] = new Literal(feature.getKey(), feature.getValue());
		}
		
		final SatSolver solver = new SatSolver(new And(formula), TIMEOUT);
		
		for (int j = 0; j < literals.length; j++) {
			Literal literal = (Literal) literals[j];			
			literal.positive = !literal.positive;
			try {
				results[j] = solver.isSatisfiable(literals[j]);
			} catch (TimeoutException e) {
				FMCorePlugin.getDefault().logError(e);
				results[j] = false;
			}
			literal.positive = !literal.positive;
		}
		return results;
	}
	
	public long number() {
		return number(250);
	}
	
	public long number(long timeout) {
		final List<Node> children = new ArrayList<Node>();
		
		for (SelectableFeature feature : features) {
			if (feature.getSelection() != Selection.UNDEFINED && !feature.getFeature().hasHiddenParent()) {
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
		features.add(sFeature);
		if (sFeature != null && sFeature.getName() != null) {
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
				if (feature.getManual() == Selection.UNDEFINED
//						|| (feature.getAutomatic() == Selection.UNDEFINED && feature.getFeature().hasHiddenParent())
						) {
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
		
//		for (SelectableFeature feature : features) {
//			if (feature.getAutomatic() == Selection.UNDEFINED && feature.getFeature().hasHiddenParent()) {
//				try {
//					if (!solver2.isSatisfiable(new Literal(feature.getFeature().getName(), false))) {
//						feature.setAutomatic(Selection.SELECTED);
//					} else if (!solver2.isSatisfiable(new Literal(feature.getFeature().getName(), true))) {
//						feature.setAutomatic(Selection.UNSELECTED);
//					} else {
//						feature.setAutomatic(Selection.UNDEFINED);
//					}
//				} catch (TimeoutException e) {
//					FMCorePlugin.getDefault().logError(e);
//				}
//			}
//		}
	}
}
