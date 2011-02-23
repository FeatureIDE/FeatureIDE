/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.configuration;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
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


public class Configuration {

	private static final int TIMEOUT = 1000;

	private SelectableFeature root;

	private ArrayList<SelectableFeature> features = new ArrayList<SelectableFeature>();

	private Hashtable<String, SelectableFeature> table = new Hashtable<String, SelectableFeature>();

	private Node rootNode;

	private FeatureModel featureModel;

	private boolean propagate;

	public Configuration(FeatureModel featureModel) {
		this(featureModel, true, false);
	}

	public Configuration(FeatureModel featureModel, boolean propagate) {
		this(featureModel, propagate, false);
	}

	public Configuration(FeatureModel featureModel, boolean propagate, boolean ignoreAbstractFeatures) {
		this.featureModel = featureModel;
		this.propagate = propagate;

		root = new SelectableFeature(this, featureModel.getRoot());
		initFeatures(root, featureModel.getRoot());

		rootNode = NodeCreator.createNodes(featureModel, ignoreAbstractFeatures);
		rootNode = rootNode.toCNF();

		updateAutomaticValues();
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
	 * Checks that all manual and automatic selections are valid.
	 * 
	 * @return
	 */
	public boolean valid() {
		LinkedList<Node> children = new LinkedList<Node>();
		for (SelectableFeature feature : features)
		    if (feature.getFeature() != null && feature.getFeature().isConcrete()) {
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
	}

	private void resetAutomaticValues() {
		for (SelectableFeature feature : features)
			feature.setAutomatic(Selection.UNDEFINED);
	}
	
	public boolean leadToValidConfiguration(SelectableFeature feature, Selection testSelection, Selection actualSelection){
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
		for (SelectableFeature feature : features)
			if (feature.getManual() != Selection.UNDEFINED) {
				Literal literal = new Literal(feature.getName());
				literal.positive = feature.getManual() == Selection.SELECTED;
				literals.add(literal);
			}
		SatSolver solver = new SatSolver(rootNode.clone(), TIMEOUT);
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

	public SelectableFeature getSelectablefeature(String name){
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

	public SelectableFeature getRoot() {
		return root;
	}

	public void resetValues() {
		for (SelectableFeature feature : features)
			feature.setManual(Selection.UNDEFINED);
		updateAutomaticValues();
	}

	public Set<Feature> getSelectedFeatures() {
		HashSet<Feature> result = new HashSet<Feature>();
		findSelectedFeatures(getRoot(), result);
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

}
