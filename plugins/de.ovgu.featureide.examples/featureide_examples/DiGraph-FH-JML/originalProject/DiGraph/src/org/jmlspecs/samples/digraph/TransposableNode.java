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

//@ model import org.jmlspecs.models.JMLNullSafe;

/** Nodes for transposable directed graphs.
 * @author Katie Becker
 * @author Gary T. Leavens
 */
// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class TransposableNode extends ValueNode {

    /*@ public normal_behavior
      @   assignable value;
      @   ensures value == v;            
      @*/
    public TransposableNode(Object v) {
        setValue(v);
    }

    /*@ also
      @   public normal_behavior
      @     requires o instanceof TransposableNode;
      @     ensures \result
      @         ==> JMLNullSafe.equals(value, ((TransposableNode)o).value);
      @ also
      @   public normal_behavior
      @     requires !(o instanceof TransposableNode);
      @     ensures \result == false;
      @*/
    public boolean equals(/*@nullable@*/ Object o) {
        return (o instanceof TransposableNode)
            && super.equals(o);
    }

    protected /*@ pure non_null @*/ String className() {
        return "TransposableNode";
    }
}
