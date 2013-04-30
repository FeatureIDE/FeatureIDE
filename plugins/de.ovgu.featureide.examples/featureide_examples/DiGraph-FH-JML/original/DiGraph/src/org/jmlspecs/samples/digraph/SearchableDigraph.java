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

import java.awt.Color;
import java.util.*;
//@ model import org.jmlspecs.models.JMLValueSet;

/** Directed graphs that are searchable.
 * @author Katie Becker
 * @author Gary T. Leavens
 */
public class SearchableDigraph extends TransposableDigraph {

    private /*@ spec_public @*/ int time; // for DFS and DFSVisit

    /** Initialize this searchable digraph to be empty. */
    /*@  public normal_behavior
      @   assignable nodes, arcs;
      @   ensures nodes.isEmpty() && arcs.isEmpty();
      @*/
    public SearchableDigraph() {
        super();
    }
  
    /* // !FIXME! -- write this in code
       public SearchableDigraph StronglyConnectedComponents() {
       DFS();
       SearchableDigraph trans = (SearchableDigraph) transpose();
       // do trans.DFS(); in decreasing order of finishing times.
       // add the vertices in the depthFirst forest formed by 
       //    trans.DFS() as a separate strongly connected componenet
       //    to the resulting graph by calling reachSet() on the vertices
       // add the appropriate arcs
       return trans;
       }
    */

    /*@ public normal_behavior
      @  assignable time, arcs, nodes;
      @  // !FIXME! complete this specification.
      @*/
    public void DFS() {
        Iterator nodes = nodeSet.iterator();
        while (nodes.hasNext()) {
            SearchableNode next = (SearchableNode) nodes.next();
            next.setColor(Color.WHITE);
            next.setPredecessor(null);
        }
        time = 0;
        while (nodes.hasNext()) {
            SearchableNode next = (SearchableNode) nodes.next();
            if (next.getColor() == Color.WHITE) {
                DFSVisit(next);
            }
        }
    }

    /*@ public normal_behavior
      @  requires u != null && u.color != null && u.color == Color.WHITE;
      @  assignable time, arcs, u.discoverTime, u.color,
      @             u.predecessor, u.finishTime;
      @  ensures u.color == Color.BLACK && u.discoverTime == \old(time + 1)
      @       && time > \old(time); // !FIXME! complete this specification.
      @*/
    public void DFSVisit(SearchableNode u) {
        u.setColor(Color.GRAY);
        time++;
        u.setDiscoverTime(time);
        Iterator arcs = arcSet.iterator();
        while (arcs.hasNext()) {
            Arc next = (Arc) arcs.next();
            if (next.getSource() == u) {
                if (((SearchableNode) next.getTarget()).getColor()
                    == Color.WHITE) {
                        ((SearchableNode) next.getTarget())
                            .setPredecessor((SearchableNode) next.getSource());
                    DFSVisit((SearchableNode) next.getTarget());
                }
            }
        }
        u.setColor(Color.BLACK);
        u.setFinishTime(time);
        time++;
    }
}
