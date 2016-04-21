/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.core.typecheck.check;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.sat4j.specs.TimeoutException;

import AST.ASTNode;
import AST.CompilationUnit;
import de.ovgu.featureide.core.typecheck.TypeChecker;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * TODO description
 * 
 * @author soenke
 */
@SuppressWarnings("rawtypes")
public abstract class AbstractTypeCheckPlugin implements ICheckPlugin {
    protected CheckPluginManager _manager;
    protected Set<Class> registered_node_types = new HashSet<Class>();

    protected String plugin_name = "AbstractCheckPlugin";

    /**
     * the nodes collected for the plug-in, sorted by feature and then by type
     */
    protected Map<Feature, Map<Class, List<ASTNode>>> nodes = new HashMap<Feature, Map<Class, List<ASTNode>>>();

    /**
     * registers the plug-in for the specific type of ASTNodes
     * 
     * @param node_type
     */
    protected void registerNodeType(Class node_type) {
	registered_node_types.add(node_type);
    }

    /**
     * Returns all nodes of a given feature the plug-in is registered for
     * 
     * @param feature
     * @return the nodes
     */
    public Map<Class, List<ASTNode>> getNodesByFeature(Feature feature) {
        return nodes.get(feature);
    }

    /**
     * Returns all nodes of the specific type, sorted by feature
     * 
     * @param the
     *            class type
     * @return the nodes, sorted by feature
     */
    public final <T> Map<Feature, List<T>> getNodesByType(Class<T> c) {
        Map<Feature, List<T>> feature_node_map = new HashMap<Feature, List<T>>();
        for (Feature f : nodes.keySet()) {
            Map<Class, List<ASTNode>> class_node_map = getNodesByFeature(f);
            if (class_node_map.containsKey(c)) {
        	List<ASTNode> nodes = class_node_map.get(c);
    
        	List<T> new_node_list = new ArrayList<T>();
    
        	for (ASTNode n : nodes) {
        	    if (c.isInstance(n)) {
        		new_node_list.add(c.cast(n));
        	    }
        	}
    
        	feature_node_map.put(f, new_node_list);
            }
        }
    
        return feature_node_map;
    }

    /**
     * Checks if, if the first feature is chosen, one of the second set of
     * features is always chosen as well
     * 
     * @param fm
     * @param feature
     * @param implies
     * @return true if the implication holds, false otherwise
     */
    public boolean checkFeatureImplication(FeatureModel fm, Feature feature,
            Set<Feature> implies) {
        if (implies.isEmpty()) {
            return false;
        }
    
        Set<Feature> set = new HashSet<Feature>();
        set.add(feature);
        try {
            return TypeChecker.checkImpliesDisjunct(fm, set, implies);
        } catch (TimeoutException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return false;
    }

    /**
     * lets the plug-in add a new {@link CheckProblem} for the plug-in manager
     * to report
     * 
     * @param problem
     */
    public void newProblem(CheckProblem problem) {
	problem.setOrigin(this);
        _manager.addProblem(problem);
    }

    @Override
    public void register(CheckPluginManager manager) {
	_manager = manager;

	registered_node_types.add(CompilationUnit.class);

	for (Class node_type : registered_node_types) {
	    _manager.registerForNodeParse(node_type, this);
	}
    }

    @Override
    public void invokeNodeParse(Feature feature, ASTNode node) {
	if (!nodes.containsKey(feature)) {
	    nodes.put(feature, new HashMap<Class, List<ASTNode>>());
	}

	Map<Class, List<ASTNode>> map = nodes.get(feature);
	if (!map.containsKey(node.getClass())) {
	    map.put(node.getClass(), new ArrayList<ASTNode>());
	}

	map.get(node.getClass()).add(node);
    }

    @Override
    public final String getName() {
	return plugin_name;
    }

    @Override
    public void resetFeature(Feature feature) {
        nodes.remove(feature);
    }
}
