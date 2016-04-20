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

//@ model import org.jmlspecs.models.*;
import java.util.*;

/** Transposable directed graphs.
 * @author Katie Becker
 * @author Gary T. Leavens
 */
// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class TransposableDigraph extends Digraph {

    /** Initialize this transposable digraph to be empty. */
    /*@  public normal_behavior
      @   assignable nodes, arcs;
      @   ensures nodes.isEmpty() && arcs.isEmpty();
      @*/
    public TransposableDigraph() {
        super();
    }

    /** Transpose this graph by inverting the direction of all its edges. */
    /*@ public normal_behavior
      @  assignable arcs;
      @  ensures nodes.equals(\old(nodes));
      @  ensures arcs.equals(flipAll(\old(arcs)));
      @*/
    public void transpose() {
        Iterator arciter = arcSet.iterator();
        while (arciter.hasNext()) {
            Arc a = (Arc) arciter.next();
            a.flip();
        }
    }

    /** Return a set with each edge inverted. */
    /*@  public model pure JMLValueSet flipAll(JMLValueSet s)
      @ {
      @     JMLValueSet ret = new JMLValueSet();
      @     JMLIterator iter = s.iterator();
      @     while (iter.hasNext()) {
      @       ArcType a = (ArcType) iter.next();
      @       ret = ret.insert(new ArcType(a.to, a.from));
      @     }
      @     return ret;
      @   }  
      @*/
}
