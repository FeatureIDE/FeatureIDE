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
import java.util.List;
import java.util.Map;

import AST.ASTNode;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * Manages the check plug-ins
 * 
 * Provides methods for the execution of checks and node iteration
 * 
 * @author Soenke Holthusen
 */
public class CheckPluginManager {
    private List<ICheckPlugin> _plugins = new ArrayList<ICheckPlugin>();
    private @SuppressWarnings("rawtypes") Map<Class, List<ICheckPlugin>> node_parse_plugins = new HashMap<Class, List<ICheckPlugin>>();

    private List<CheckProblem> problems = new ArrayList<CheckProblem>();
    /**
     * initiates the plug-in manager with the given plug-ins
     * 
     * @param plugins
     *            the plug-ins to be registered for checks
     */
    public CheckPluginManager(List<ICheckPlugin> plugins) {
	for (ICheckPlugin plugin : plugins) {
	    add(plugin);
	}
    }

    private void add(ICheckPlugin plugin) {
	plugin.register(this);
	_plugins.add(plugin);
    }

    /**
     * Invokes a check in every registered plug-in
     * 
     * @param fm
     */
    public void invokeChecks(FeatureModel fm) {
	resetProblems();
	for (ICheckPlugin plugin : _plugins) {
	    plugin.init();
	    plugin.invokeCheck(fm);
	}
    }

    /**
     * Registers a check plug-in for a specific ASTNode
     * 
     * @param node
     *            The node type the plug-in registers for
     * @param plugin
     *            the plug-in itself
     */
    public void registerForNodeParse(@SuppressWarnings("rawtypes") Class node, ICheckPlugin plugin) {
	if (!node_parse_plugins.containsKey(node)) {
	    node_parse_plugins.put(node, new ArrayList<ICheckPlugin>());
	}
	List<ICheckPlugin> list = node_parse_plugins.get(node);
	list.add(plugin);
    }

    /**
     * Delivers an ASTNode to the registered plug-ins
     * 
     * @param feature
     *            the feature the node is associated with
     * @param node
     *            the node to
     */
    public void invokeNodeParse(Feature feature, @SuppressWarnings("rawtypes") ASTNode node) {
	List<ICheckPlugin> list = node_parse_plugins.get(node.getClass());
	if (list != null) {
	    for (ICheckPlugin plugin : list) {
		plugin.invokeNodeParse(feature, node);
	    }
	}
    }

    /**
     * resets the data about a feature to prepare a re-parse
     * 
     * @param feature
     */
    public void resetFeature(Feature feature) {
	for (ICheckPlugin plugin : _plugins) {
	    plugin.resetFeature(feature);
	}
    }

    /**
     * resets the problems of the last iteration
     */
    public void resetProblems() {
	problems = new ArrayList<CheckProblem>();
    }

    /**
     * let's a plug-in report a problem to the plug-in manager
     * 
     * @param problem
     * @param plugin
     */
    public void addProblem(CheckProblem problem) {
	problems.add(problem);
    }

    
    public List<CheckProblem> getProblems(){
	return problems;
    }
}
