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
package de.ovgu.featureide.fm.core;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * Calculates dependencies of features
 * 
 * @author Soenke Holthusen
 * 
 */
public class FeatureDependencies {
    private static final String LEGEND_TEXT = "X ALWAYS Y := If X is selected then Y is selected in every valid configuration."
	    + "\n"
	    + "X MAYBE  Y := If X is selected then Y is selected in at least one but not all valid configurations. "
	    + "\n"
	    + "X NEVER  Y := If X is selected then Y cannot be selected in any valid configuration."
	    + "\n";

    private FeatureModel fm;
    private Node rootNode;
    
    private Map<Feature, Set<Feature>> always = new HashMap<Feature, Set<Feature>>();
    private Map<Feature, Set<Feature>> never = new HashMap<Feature, Set<Feature>>();
    private Map<Feature, Set<Feature>> maybe = new HashMap<Feature, Set<Feature>>();

    /**
     * @param fm
     */
    public FeatureDependencies(FeatureModel fm) {
		this(fm, true);
    }
    
    /**
     * This constructor has the option to not calculate all dependencies automatically.
     * @param fm The feature model
     * @param calculateDependencies <code>true</code> if dependencies should be calculated
     */
    public FeatureDependencies(FeatureModel fm, boolean calculateDependencies) {
		this.fm = fm;
		this.rootNode = createRootNode(fm);
		if (calculateDependencies) {
			calculateDependencies();
		}
    }

    /**
     * calculates feature dependencies
     */
    private void calculateDependencies() {
		for (Feature feature : fm.getFeatures()) {
		    always.put(feature, new HashSet<Feature>());
		    never.put(feature, new HashSet<Feature>());
		    maybe.put(feature, new HashSet<Feature>());
	
		    Node nodeSel = new And(rootNode, new Literal(feature.getName()));
	
		    for (Feature current_feature : fm.getFeatures()) {
				if (!current_feature.equals(feature)) {
				    try {
						if (nodeImpliesFeature(nodeSel, current_feature.getName(), true)) {
						    always.get(feature).add(current_feature);
						} else if (nodeImpliesFeature(nodeSel, current_feature.getName(), false)) {
						    never.get(feature).add(current_feature);
						} else {
						    maybe.get(feature).add(current_feature);
						}
				    } catch (TimeoutException e) {
				    	FMCorePlugin.getDefault().logError(e);
				    }
				}
		    }
		}
    }
    
    
    
    /**
     * Gets all implied features of the given feature
     * @param feature
     * @return all implied features
     */
    public Collection<Feature> getImpliedFeatures(Feature feature) {
    	if (always.containsKey(feature)) {
    		return always.get(feature);
    	}
    	always.put(feature, new HashSet<Feature>());
    	Node nodeSel = new And(rootNode, new Literal(feature.getName()));
    	Collection<Feature> impliedFeatures = always.get(feature);
    	try {
    		for (Feature f : fm.getFeatures()) {
    			if (!f.equals(feature)) {
					if (nodeImpliesFeature(nodeSel, f.getName(), true)) {
					    impliedFeatures.add(f);
					}
    			}
    		}
    	} catch (TimeoutException e) {
			FMCorePlugin.getDefault().logError(e);
		}
    	return impliedFeatures;
    }
    
    /**
	 * @param A Feature
	 * @param B Feature
	 * @return <code>true</code> if A implies B
	 */
	public boolean isAlways(Feature A, Feature B) {
		if (always.containsKey(A)) {
			return always.get(A).contains(B);
		}
		Node nodeSel = new And(rootNode, new Literal(A.getName()));
		try {
			return nodeImpliesFeature(nodeSel, B.getName(), true);
		} catch (TimeoutException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return false;
	}
    
    /**
     * creates the Node representation of the featureModel
     * 
     * @param fm
     *            featureModel
     * @return Node representing the featureModel
     */
    private  Node createRootNode(FeatureModel fm) {
		return NodeCreator.createNodes(fm, true).toCNF();
    }

    /**
     * @param node
     * @param s
     * @param positive
     *            if false, the feature is negated
     * @return true if the given feature is selected in every valid
     *         configuration for the featureModel represented by node
     * @throws TimeoutException
     */
    private  boolean nodeImpliesFeature(Node node, String featureName, boolean positive) throws TimeoutException {
    	Node nodeNeg = null;
    	if (positive) { 
    		nodeNeg = new Not((new Implies(node, new Literal(featureName))));
    	} else {
    		nodeNeg = new Not((new Implies(node, new Not(featureName))));
    	}
    	return !new SatSolver(nodeNeg, 2500).isSatisfiable();
    }
    
    /**
     * @param feature
     * @return
     */
    public Set<Feature> always(Feature feature) {
    	return always.get(feature);
    }

    /**
     * @param feature
     * @return
     */
    public Set<Feature> never(Feature feature) {
    	return never.get(feature);
    }

    /**
     * @param feature
     * @return
     */
    public Set<Feature> maybe(Feature feature) {
    	return maybe.get(feature);
    }

    public String toString() {
    	StringBuilder builder = new StringBuilder();
		for (Feature feature : fm.getFeatures()) {
		    builder.append("\n");
		    for (Feature f : always.get(feature)) {
				builder.append(feature.getName() + " ALWAYS " + f.getName() + "\n");
		    }
		    for (Feature f : never.get(feature)) {
				builder.append(feature.getName() + " NEVER " + f.getName() + "\n");
		    }
		    for (Feature f : maybe.get(feature)) {
				builder.append(feature.getName() + " MAYBE " + f.getName() + "\n");
		    }
		}
		return builder.toString();
    }
    
    public String toStringWithLegend(){
    	return LEGEND_TEXT + toString();
    }

}
