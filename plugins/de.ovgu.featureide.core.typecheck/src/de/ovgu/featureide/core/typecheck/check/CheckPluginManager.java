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

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.typecheck.parser.ClassTable;

/**
 * TODO description
 * 
 * @author S�nke Holthusen
 */
public class CheckPluginManager extends Observable {
	private ArrayList<ICheckPlugin> _plugins;
	private Map<String, List<ICheckPlugin>> node_parse_plugins = new HashMap<String, List<ICheckPlugin>>();

	public CheckPluginManager() {
		_plugins = new ArrayList<ICheckPlugin>();
	}

	public CheckPluginManager(ICheckPlugin... plugins) {
		this();

		for (ICheckPlugin plugin : plugins) {
			add(plugin);
		}
	}

	public void addCheck(ICheckPlugin plugin) {
		add(plugin);
	}

	public void addCheck(ICheckPlugin... plugins) {
		for (ICheckPlugin plugin : plugins) {
			add(plugin);
		}
	}

	private void add(ICheckPlugin plugin){
		plugin.register(this);
		_plugins.add(plugin);
	}
	
	public void invokeChecks(IFeatureProject project, ClassTable class_table) {
		for (ICheckPlugin plugin : _plugins) {
			plugin.invokeCheck(project, class_table);
		}
	}

	public void registerForNodeParse(String node, ICheckPlugin plugin) {
		System.out.println("registering for: " + node);
		List<ICheckPlugin> list = node_parse_plugins.get(node);
		if (list == null) {
			list = new ArrayList<ICheckPlugin>();
			node_parse_plugins.put(node, list);
		}
		list.add(plugin);
	}

	public void invokeNodeParse(ASTNode node) {
		String node_name = node.getClass().getCanonicalName();
		List<ICheckPlugin> list = node_parse_plugins.get(node_name);
		if (list == null) {
			//System.out.println("PluginManager: nobody interested in: " + node_name);
			return;
		} else {
			//System.out.println("CheckPluginManager: found plugins for: " + node_name);
			for (ICheckPlugin plugin : list) {
				plugin.invokeNodeParse(node);
			}
		}
	}
}
