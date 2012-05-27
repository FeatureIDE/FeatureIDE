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
package de.ovgu.featureide.core.typecheck.check;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Observable;

import AST.ASTNode;
import AST.ClassDecl;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.typecheck.parser.ClassTable;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * Manages the check plug-ins
 * 
 * Provides methods for the execution of checks and node iterating
 * 
 * @author S�nke Holthusen
 */
public class CheckPluginManager extends Observable {
    private ArrayList<ICheckPlugin> _plugins = new ArrayList<ICheckPlugin>();
    private Map<Class, List<ICheckPlugin>> node_parse_plugins = new HashMap<Class, List<ICheckPlugin>>();

    private Map<CheckProblem, ICheckPlugin> problems = new HashMap<CheckProblem, ICheckPlugin>();

    /**
     * @author S�nke Holthusen
     * 
     * 
     * 
     * @param plugins
     *            the plug-ins to be registered for checks
     */
    public CheckPluginManager(ICheckPlugin... plugins) {
	addCheck(plugins);
    }

    private void addCheck(ICheckPlugin... plugins) {
	for (ICheckPlugin plugin : plugins) {
	    add(plugin);
	}
    }

    private void add(ICheckPlugin plugin) {
	plugin.register(this);
	_plugins.add(plugin);
    }

    /**
     * @author S�nke Holthusen
     * 
     *         Invokes a check in every registered plug-in
     * 
     * @param project
     * @param class_table
     */
    public void invokeChecks(FeatureModel fm) {
	resetProblems();
	for (ICheckPlugin plugin : _plugins) {
	    plugin.init();
	    plugin.invokeCheck(fm);
	}
	reportproblems();
    }

    /**
     * @author S�nke Holthusen
     * 
     *         Registers a check plug-in for a specific ASTNode
     * 
     * @param node
     *            The node type the plug-in registers for
     * @param plugin
     *            the plug-in itself
     */
    public void registerForNodeParse(Class node, ICheckPlugin plugin) {
	if (!node_parse_plugins.containsKey(node)) {
	    node_parse_plugins.put(node, new ArrayList<ICheckPlugin>());
	}
	List<ICheckPlugin> list = node_parse_plugins.get(node);
	list.add(plugin);
    }

    /**
     * @author S�nke Holthusen
     * 
     *         Delivers an ASTNode to the registered plug-ins
     * 
     * @param feature
     *            the feature the node is associated with
     * @param node
     *            the node to
     */
    public void invokeNodeParse(Feature feature, ASTNode node) {
	List<ICheckPlugin> list = node_parse_plugins.get(node.getClass());
	if (list != null) {
	    for (ICheckPlugin plugin : list) {
		plugin.invokeNodeParse(feature, node);
	    }
	}
    }

    public void resetFeature(Feature feature) {
	for (ICheckPlugin plugin : _plugins) {
	    plugin.resetFeature(feature);
	}
    }

    public void resetProblems(){
	problems = new HashMap<CheckProblem, ICheckPlugin>();
    }
    
    public void addProblem(CheckProblem problem, ICheckPlugin plugin) {
	problems.put(problem, plugin);
    }

    public void reportproblems() {
	for (CheckProblem problem : problems.keySet()) {
	    System.out.println(problems.get(problem).getName() + " reported a Problem:");
	    System.out.println(problem);
	}
    }
}
