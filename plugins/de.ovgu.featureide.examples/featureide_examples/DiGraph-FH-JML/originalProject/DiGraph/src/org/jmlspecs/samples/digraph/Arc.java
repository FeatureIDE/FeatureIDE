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

/** Directed arcs for directed graphs.
 * @author Katie Becker
 * @author Gary T. Leavens
 */
public class Arc implements Cloneable {

    private /*@ spec_public non_null @*/ NodeType source;
    private /*@ spec_public non_null @*/ NodeType target;
    
    //@ private invariant_redundantly source != null && target != null;

    /** Initialize this arc with the given source and target. */
    /*@ public normal_behavior
      @   requires_redundantly source != null && target != null;
      @   assignable this.source, this.target;
      @   ensures this.source == source
      @        && this.target == target;
      @*/
    public Arc(NodeType source, NodeType target) {
        this.source = source;
        this.target = target;
    }

    /*@ also
      @   public normal_behavior
      @     requires o instanceof Arc;
      @     ensures \result
      @             ==> ((Arc)o).source.equals(this.source)
      @                 && ((Arc)o).target.equals(this.target);
      @ also
      @   public normal_behavior
      @     requires !(o instanceof Arc);
      @     ensures \result == false;
      @*/
    public /*@nullable@*/ Object o) {
        return (o instanceof Arc) 
            && ((Arc)o).source.equals(source)
            && ((Arc)o).target.equals(target);
    }

    /*@ also
      @   public normal_behavior
      @     ensures \result instanceof Arc
      @         && ((Arc)\result).equals(this);
      @*/
    public /*@ pure @*/ Object clone() {
        Arc res;
        try {
            res = (Arc)super.clone();
        } catch (CloneNotSupportedException e) {
            // should not happen
            throw new InternalError(e.getMessage());
        }
	// source and target refs are shared between object and clone
	// so they do not need to be reassigned
	//@ assume res.source == source && res.target == target;
	return res;
    }
    
    public /*@ pure @*/ int hashCode() {
        return source.hashCode() + target.hashCode();
    }

    /** Invert the direction of this arc. */
    /*@ public normal_behavior
      @   assignable source, target;
      @   ensures source == \old(target) && target == \old(source);
      @*/
    public void flip() {
        NodeType temp = source;
        source = target;
        target = temp;
    }

    /** Get the source node of this arc. */
    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == source;           
      @*/
    public /*@ pure @*/ NodeType getSource() {
        return source;
    }

    /** Set the source node of this arc to the given node. */
    /*@ public normal_behavior
      @   requires_redundantly source != null;
      @   assignable this.source;
      @   ensures this.source == source;           
      @*/
    public void setSource(NodeType source) {
        this.source = source;
    }

    /** Get the target node of this arc. */
    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == target;           
      @*/
    public /*@ pure @*/ NodeType getTarget() {
        return target;
    }

    /** Set the target node of this arc to the given node. */
    /*@ public normal_behavior
      @   requires_redundantly target != null;
      @   assignable this.target;
      @   ensures this.target == target;           
      @*/
    public void setTarget(NodeType target) {
        this.target = target;
    }

    /** Return the name of this class. */
    //@ ensures \result != null;
    protected /*@ pure @*/ String className() {
        return "Arc";
    }

    public String toString() {
        return className() + "[from: " + source + ", to: " + target + "]";
    }
}
