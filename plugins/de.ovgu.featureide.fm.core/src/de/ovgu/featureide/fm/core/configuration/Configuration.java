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
import java.util.HashSet;
import java.util.Hashtable;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
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

	private SelectableFeature root;

	private ArrayList<SelectableFeature> features = new ArrayList<SelectableFeature>();

	private Hashtable<String, SelectableFeature> table = new Hashtable<String, SelectableFeature>();

	private Node rootNode;

	private FeatureModel featureModel;

	private boolean propagate;

	public Configuration(FeatureModel featureModel) {
		this(featureModel, true);
	}

	public Configuration(FeatureModel featureModel, boolean propagate) {
		this(featureModel, propagate, true);
	}

	public Configuration(FeatureModel featureModel, boolean propagate,
			boolean ignoreAbstractFeatures) {
		this.featureModel = featureModel;
		this.propagate = propagate;

		Feature root2 = featureModel.getRoot();
		root = new SelectableFeature(this, root2);
		initFeatures(root, root2);

		rootNode = NodeCreator
				.createNodes(featureModel, ignoreAbstractFeatures);
		rootNode = rootNode.toCNF();

		updateAutomaticValues();
	}
	
	/**
	 * This method creates a clone of the given {@link Configuration}
	 * @param configuration The configuration to clone
	 */
	public Configuration(Configuration configuration) {
		this(configuration, configuration.featureModel, false);
	}
	
	public Configuration(Configuration configuration, FeatureModel featureModel, boolean propagate) {
		this.featureModel = featureModel;
		this.propagate = false;

		Feature root2 = featureModel.getRoot();
		root = new SelectableFeature(this, root2);
		initFeatures(root, root2);

		rootNode = NodeCreator
				.createNodes(featureModel, false);
		rootNode = rootNode.toCNF();
		
		for (SelectableFeature f : configuration.features) {
			setManual(f.getName(), f.getSelection());
		}
		this.propagate = propagate;
	}

	/**
	 * if there are hidden features which Selection is UNDEFINED, they are
	 * selected automatically
	 */
	private void updateHiddenFeatureValues() {
		// try selecting each hidden feature that still are UNDEFINED
		for (SelectableFeature feature : features) {

			boolean hasHiddenParent = feature.getFeature().hasHiddenParent();
			boolean isUndefined = feature.getSelection() == Selection.UNDEFINED;

			if (hasHiddenParent && isUndefined) {
				feature.setAutomatic(Selection.UNSELECTED);
				if (!valid()) {
					feature.setAutomatic(Selection.SELECTED);
					
					if (!valid()) {
						
						feature.setAutomatic(Selection.UNDEFINED);

					}
				}
			}
		}
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

	/**
	 * Checks that all manual and automatic selections are valid.<br>
	 * Abstract features will <code>not</code> be ignored.
	 * @return <code>true</code> if the current selection is satisfiable
	 */
	public boolean valid() {
		LinkedList<Node> children = new LinkedList<Node>();
		for (SelectableFeature feature : features)
			if (feature.getFeature() != null) {
				Literal literal = new Literal(feature.getName());
				literal.positive = feature.getSelection() == Selection.SELECTED;
				children.add(literal);
			}
		try {
			return new SatSolver(rootNode, TIMEOUT).isSatisfiable(children);
		} catch (TimeoutException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return false;
	}

	public long number() {
		return number(250);
	}

	public long number(long timeout) {
		LinkedList<Node> children = new LinkedList<Node>();
		for (SelectableFeature feature : features)
			if (!feature.hasChildren()) {
				if (feature.getSelection() == Selection.SELECTED)
					children.add(new Literal(feature.getName(), true));
				if (feature.getSelection() == Selection.UNSELECTED)
					children.add(new Literal(feature.getName(), false));
			}
		Node node = new And(rootNode.clone(), new And(children));
		return new SatSolver(node, timeout).countSolutions();
	}

	private void updateAutomaticValues() {
		if (!propagate)
			return;
		resetAutomaticValues();

		updateManualDefinedValues();
		updateManualUndefinedValues();
		updateHiddenFeatureValues();

	}

	private void resetAutomaticValues() {
		for (SelectableFeature feature : features) {

			feature.setAutomatic(Selection.UNDEFINED);

		}
	}

	public boolean leadToValidConfiguration(SelectableFeature feature,
			Selection testSelection, Selection actualSelection) {
		feature.setManual(testSelection);
		updateAutomaticValues();
		if (valid()) {
			feature.setManual(actualSelection);
			updateAutomaticValues();
			return true;
		}
		feature.setManual(actualSelection);
		updateAutomaticValues();
		return false;
	}

	private void updateManualDefinedValues() {
		List<Node> literals = new LinkedList<Node>();
		// each feature that is not manually defined is added to "literals"
		for (SelectableFeature feature : features)
			if (feature.getManual() != Selection.UNDEFINED) {
				Literal literal = new Literal(feature.getName());
				literal.positive = feature.getManual() == Selection.SELECTED;
				literals.add(literal);
			}
		SatSolver solver = new SatSolver(rootNode.clone(), TIMEOUT);
		// for each feature: if negating it is not possible, the feature will be
		// set as manual defined

		for (Node node : literals) {
			Literal literal = (Literal) node;
			literal.positive = !literal.positive;
			try {
				if (!solver.isSatisfiable(literals)) {
					SelectableFeature feature = table.get(literal.var);
					feature.setAutomatic(feature.getManual());
				}
			} catch (TimeoutException e) {
				FMCorePlugin.getDefault().logError(e);
			}
			literal.positive = !literal.positive;
		}
	}

	private void updateManualUndefinedValues() {
		List<Node> children = new LinkedList<Node>();
		for (SelectableFeature feature : features)
			if (feature.getManual() != Selection.UNDEFINED) {
				Literal literal = new Literal(feature.getName());
				literal.positive = feature.getManual() == Selection.SELECTED;
				children.add(literal);
			}
		Node node = new And(rootNode.clone(), new And(children));
		SatSolver solver = new SatSolver(node, TIMEOUT);
		for (Literal literal : solver.knownValues()) {
			SelectableFeature feature = table.get(literal.var);
			if (feature != null && feature.getManual() == Selection.UNDEFINED)
				feature.setAutomatic(literal.positive ? Selection.SELECTED
						: Selection.UNSELECTED);

		}

	}

	public void setManual(SelectableFeature feature, Selection selection) {
		feature.setManual(selection);
		updateAutomaticValues();
	}
	public void setAutomatic(SelectableFeature feature, Selection selection) {
		feature.setAutomatic(selection);
		updateAutomaticValues();
	}
	public SelectableFeature getSelectablefeature(String name) {
		SelectableFeature feature = table.get(name);
		if (feature == null)
			return null;
		return feature;
	}

	public void setManual(String name, Selection selection) {
		SelectableFeature feature = table.get(name);
		if (feature == null)
			throw new FeatureNotFoundException();
		setManual(feature, selection);
	}
	
	public void setAutomatic(String name, Selection selection) {
		SelectableFeature feature = table.get(name);
		if (feature == null)
			throw new FeatureNotFoundException();
		setAutomatic(feature, selection);
	}
	
	public SelectableFeature getRoot() {
		return root;
	}

	public void resetValues() {
		for (SelectableFeature feature : features)
			feature.setManual(Selection.UNDEFINED);
		updateAutomaticValues();
	}

	public Set<Feature> getSelectedFeatures() {
		HashSet<Feature> result = new LinkedHashSet<Feature>();
		findSelectedFeatures(getRoot(), result);
		return result;
	}
	
	public Set<String> getSelectedFeatureNames() {
		final Set<Feature> selectedFeatures = getSelectedFeatures();
		final Set<String> result = new LinkedHashSet<String>();
		
		for (final Feature feature : selectedFeatures) {
			result.add(feature.getName());
		}
		return result;
	}

	private void findSelectedFeatures(SelectableFeature sf,
			HashSet<Feature> result) {
		if (sf.getSelection() == Selection.SELECTED)
			result.add(sf.getFeature());
		for (TreeElement child : sf.getChildren())
			findSelectedFeatures((SelectableFeature) child, result);
	}

	public Set<Feature> getUnSelectedFeatures() {
		HashSet<Feature> result = new HashSet<Feature>();
		findUnSelectedFeatures(getRoot(), result);
		return result;
	}

	private void findUnSelectedFeatures(SelectableFeature sf,
			HashSet<Feature> result) {
		if (sf.getSelection() == Selection.UNSELECTED)
			result.add(sf.getFeature());
		for (TreeElement child : sf.getChildren())
			findUnSelectedFeatures((SelectableFeature) child, result);
	}

	public FeatureModel getFeatureModel() {
		return featureModel;
	}

	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();
		for (Feature f : getSelectedFeatures()) {
			if (f.isAbstract()) {
				continue;
			}
			builder.append(f.getName());
			builder.append("\r\n");
		}
		return builder.toString();
	}
	
	public LinkedList<List<String>> getSolutions(int max) throws TimeoutException {
		LinkedList<Node> children = new LinkedList<Node>();

		for (Feature feature : getSelectedFeatures()) {
			children.add(new Literal(feature.getName(), true));
		}
		
		for (Feature feature : getUnSelectedFeatures()) {
			children.add(new Literal(feature.getName(), false));
		}

		Node node = new And(rootNode.clone(), new And(children));

		LinkedList<List<String>> solutionList = new SatSolver(node, 2002).getSolutionFeatures(max);
		
		return solutionList;
	}
	
	public ArrayList<SelectableFeature> getFeatures() {
		return features;
	}
}
