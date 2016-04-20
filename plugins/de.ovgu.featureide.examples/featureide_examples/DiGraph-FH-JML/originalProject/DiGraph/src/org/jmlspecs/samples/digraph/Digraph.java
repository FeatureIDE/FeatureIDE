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

package org.jmlspecs.samples.digraph;

//@ refine "Digraph.jml";

import java.util.*;
//@ model import org.jmlspecs.models.*;

/** Directed graphs.
 * @author Katie Becker
 * @author Gary T. Leavens
 */
public abstract class Digraph {

    protected /*@ spec_public @*/ HashSet nodeSet;
    //@                           in nodes;
    //@                           maps nodeSet.theSet \into nodes;
    protected /*@ spec_public @*/ HashSet arcSet;
    //@                           in arcs;
    //@                           maps arcSet.theSet \into arcs;

    //@ private represents nodes <- JMLValueSet.convertFrom(nodeSet);
    //@ private represents arcs <- arcAbstractValue(arcSet);

    /*@ private invariant_redundantly nodeSet != null;
      @ private invariant (\forall Object e; nodeSet.contains(e); 
      @                       e!=null && e instanceof NodeType);
      @ 
      @ private invariant_redundantly arcSet != null;
      @ private invariant (\forall Object e; arcSet.contains(e); 
      @                       e!=null && e instanceof Arc);
      @*/

    public Digraph() {
        nodeSet = new HashSet();
        arcSet = new HashSet();
    }

    public void addNode(NodeType n) {
        nodeSet.add(n);
    }

    public void removeNode(NodeType n) {
        nodeSet.remove(n);
    }

    public void addArc(NodeType inFrom, NodeType inTo) {
        arcSet.add(new Arc(inFrom, inTo));
    }

    public void removeArc(NodeType inFrom, NodeType inTo) {
        arcSet.remove(new Arc(inFrom, inTo));
    }

    /*@ also 
      @  public normal_behavior
      @    ensures \result == nodeSet.contains(n);
      @*/
    public /*@ pure @*/ boolean isNode(NodeType n) {
        return nodeSet.contains(n);
    }

    public /*@ pure @*/ boolean isArc(NodeType inFrom, NodeType inTo) {
        return arcSet.contains(new Arc(inFrom, inTo));
    }

    public /*@ pure @*/ boolean isAPath(NodeType start, NodeType end) {
        return reachSet(start).contains(end);
    }

    protected /*@ pure @*/ HashSet reachSet(NodeType start) {
        HashSet disc = new HashSet(); // discovered vertices
        Iterator arcs = arcSet.iterator();
        while (arcs.hasNext()) {
            Arc next = (Arc) arcs.next();
            if (next.getSource() == start && !disc.contains(next.getTarget())) {
                disc.add(next.getTarget());
                reachSet(next.getTarget());
            }
        }

        return disc;
    }
  
    /*@ private pure model JMLValueSet arcAbstractValue(HashSet arcs) {
      @   JMLValueSet ret = new JMLValueSet();
      @   Iterator arcIter = arcs.iterator();
      @   while (arcIter.hasNext()) {
      @     Arc a = (Arc) arcIter.next();
      @     NodeType from = a.getSource();
      @     NodeType to = a.getTarget();
      @     ret = ret.insert(new ArcType(from, to));
      @   }
      @   return ret;
      @ }
      @*/

    public String toString() {
        return "[arcs: " + arcSet.toString()
               + "\n nodes: " + nodeSet.toString() + "]";
    }

    public /*@ pure @*/ boolean unconnected(NodeType n) {
        Iterator arcIter = arcSet.iterator();
        while (arcIter.hasNext()) {
            Arc a = (Arc) arcIter.next();
            if (a.getSource().equals(n) || a.getTarget().equals(n)) {
                return false;
            }
        }
        return true;
    }
}
