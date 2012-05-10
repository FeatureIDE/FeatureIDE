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
import java.util.Observer;

import de.ovgu.featureide.fm.core.Feature;

import AST.ASTNode;

/**
 * TODO description
 * 
 * @author soenke
 */
public abstract class AbstractCheckPlugin implements ICheckPlugin
{
	protected CheckPluginManager _manager;
	protected List<Class> registered_node_types = new ArrayList<Class>();
	
	/*
	 * Feature 	-> Node Type 	-> Data
	 * 							   Data
	 * 			-> Node Type	-> Data
	 * 							   Data
	 * 							   Data
	 * Feature	-> Node Type	-> Data
	 * ...
	 */
	protected Map<String, Map<Class, List<ASTNode>>> nodes = new HashMap<String, Map<Class,List<ASTNode>>>();
	
	protected void registerNodeType(Class node_type){
		registered_node_types.add(node_type);
	}
	
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.typecheck.check.ICheckPlugin#register(de.ovgu.featureide.core.typecheck.check.CheckPluginManager)
	 */
	@Override
	public void register(CheckPluginManager manager)
	{
		_manager = manager;
		
		for(Class node_type : registered_node_types){
			_manager.registerForNodeParse(node_type, this);
		}
		
		init();
	}
	
	public void invokeNodeParse(Feature feature, ASTNode node){
		Map<Class, List<ASTNode>> map = nodes.get(feature.getName());
		if(map == null){
			map = new HashMap<Class, List<ASTNode>>();
			nodes.put(feature.getName(), map);
		}
		
		ASTNode moo = new ASTNode<ASTNode>();
	}
	
	public void init(){}
}
