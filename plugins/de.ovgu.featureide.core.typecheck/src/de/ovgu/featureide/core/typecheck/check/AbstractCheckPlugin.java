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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import AST.ASTNode;
import AST.CompilationUnit;
import de.ovgu.featureide.fm.core.Feature;

/**
 * TODO description
 * 
 * @author soenke
 */
@SuppressWarnings("rawtypes")
public abstract class AbstractCheckPlugin implements ICheckPlugin {
	protected CheckPluginManager _manager;
	protected Set<Class> registered_node_types = new HashSet<Class>();

	protected String plugin_name = "AbstractCheckPlugin";

	/*
	 * Feature -> Node Type -> Data Data -> Node Type -> Data Data Data Feature
	 * -> Node Type -> Data ...
	 */
	protected Map<Feature, Map<Class, List<ASTNode>>> nodes = new HashMap<Feature, Map<Class, List<ASTNode>>>();
	protected List<Feature> features = new ArrayList<Feature>();

	protected void registerNodeType(Class node_type) {
		registered_node_types.add(node_type);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.core.typecheck.check.ICheckPlugin#register(de.ovgu
	 * .featureide.core.typecheck.check.CheckPluginManager)
	 */
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
		features.add(feature);
	}

	public Map<Class, List<ASTNode>> getNodesByFeature(Feature feature) {
		return nodes.get(feature);
	}

	public <T> Map<Feature, List<T>> getNodesByType(Class<T> c) {
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

	@Override
	public String getName() {
		return plugin_name;
	}
	
	public boolean checkFeatureImplication(Feature feature, List<Feature> implies){
	    return false;
	}
}
