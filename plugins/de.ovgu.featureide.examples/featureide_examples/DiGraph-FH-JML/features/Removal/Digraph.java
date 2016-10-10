// Copyright (C) 2003 Iowa State University

// This file is part of JML

// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.

// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

import java.util.*;

/** Directed graphs.
 * @author Katie Becker
 * @author Gary T. Leavens
 */
public class Digraph {

	 /*@  public normal_behavior
	   @   requires unconnected(n);
	   @   assignable nodes;
	   @   ensures nodes.equals(\old(nodes.remove(n)));
	   @*/
    public void removeNode(NodeType n) {
        nodeSet.remove(n);
    }

	 /*@  public normal_behavior
	   @   requires_redundantly inFrom != null && inTo != null;
	   @   requires nodes.has(inFrom) && nodes.has(inTo);
	   @   assignable arcs;
	   @   ensures arcs.equals(
	   @            \old(arcs).remove(new ArcType(inFrom, inTo)));
	   @*/
    public void removeArc(NodeType inFrom, NodeType inTo) {
        arcSet.remove(new Arc(inFrom, inTo));
    }

}
