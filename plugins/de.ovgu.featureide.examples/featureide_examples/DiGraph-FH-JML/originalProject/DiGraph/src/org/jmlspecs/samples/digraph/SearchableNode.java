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

import java.awt.Color;

/** Nodes for searchable graphs.
 * @author Katie Becker
 * @author Gary T. Leavens
 */
public class SearchableNode extends ValueNode {

    private /*@ spec_public @*/ int discoverTime;
    private /*@ spec_public @*/ int finishTime;
    private /*@ spec_public nullable @*/ SearchableNode predecessor;
    private /*@ spec_public nullable @*/ Color color;

    /*@ public normal_behavior
      @   assignable value;
      @   ensures value == v;            
      @*/
    public SearchableNode(/*@nullable@*/ Object v) {
        value = v;
    }

    /*@ protected normal_behavior
      @   assignable value, discoverTime, finishTime, predecessor, color;
      @   ensures value == v && discoverTime == dT && finishTime == fT
      @                     && predecessor == pred 
      @                     && JMLNullSafe.equals(color,c);           
      @*/
    protected SearchableNode(/*@nullable@*/ Object v, int dT, int fT, 
			     /*@nullable@*/ SearchableNode pred,
                             /*@nullable@*/ Color c)
    {
        value = v;
        discoverTime = dT;
        finishTime = fT;
        predecessor = pred;
        color = c;
    }

    /*@ also
      @   public normal_behavior
      @     requires o instanceof SearchableNode;
      @     ensures \result ==>
      @             JMLNullSafe.equals(value, ((SearchableNode) o).value)
      @          && discoverTime == ((SearchableNode) o).discoverTime
      @          && finishTime == ((SearchableNode) o).finishTime
      @          && JMLNullSafe.equals(predecessor,
      @                                ((SearchableNode) o).predecessor)
      @          && JMLNullSafe.equals(color, ((SearchableNode) o).color);
      @ also
      @   public normal_behavior
      @     requires !(o instanceof SearchableNode);
      @     ensures \result == false;
      @*/
    public boolean equals(/*@nullable@*/ Object o) {
        if (!(o instanceof SearchableNode)) {
            return false;
        }

        SearchableNode sn = (SearchableNode) o;
        return super.equals(o)
            && discoverTime == sn.discoverTime
            && finishTime == sn.finishTime
            && (((predecessor == null && sn.predecessor == null))
                || (predecessor != null 
                    && predecessor.equals(sn.predecessor)))
            && (((color == null && sn.color == null))
                || (color != null && color.equals(sn.color)));
    }

    // specification and comment inherited
    public int hashCode() {
        return super.hashCode() + discoverTime + finishTime;
    }

    /*@ also
      @   public normal_behavior
      @     ensures \result instanceof SearchableNode && \fresh(\result)
      @          && ((SearchableNode)\result).equals(this);
      @     ensures_redundantly \result != this;
      @*/
    public Object clone() {
        return super.clone();
    }

    /*@ protected normal_behavior
      @   assignable color;
      @   ensures color.equals(c);           
      @*/
    protected void setColor(/*@nullable@*/ Color c) {
        this.color = c;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result != null ==> \result.equals(color);           
      @*/
    public /*@ pure nullable @*/ Color getColor() {
        return color;
    }

    /*@ protected normal_behavior
      @   assignable predecessor;
      @   ensures predecessor == p;           
      @*/
    protected void setPredecessor(/*@nullable@*/ SearchableNode p) {
        this.predecessor = p;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == predecessor;           
      @*/
    public /*@ pure nullable @*/ SearchableNode getPredecessor() {
        return predecessor;
    }

    /*@ protected normal_behavior
      @   assignable finishTime;
      @   ensures finishTime == fTime;           
      @*/
    protected void setFinishTime(int fTime) {
        this.finishTime = fTime;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == finishTime;           
      @*/
    public /*@ pure @*/ int getFinishTime() {
        return finishTime;
    }

    /*@ protected normal_behavior
      @   assignable discoverTime;
      @   ensures discoverTime == dTime;           
      @*/
    protected void setDiscoverTime(int dTime) {
        this.discoverTime = dTime;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == discoverTime;           
      @*/
    public /*@ pure @*/ int getDiscoverTime() {
        return discoverTime;
    }

    protected /*@ non_null @*/ String className() {
        return "SearchableNode";
    }

    public /*@ non_null @*/ String toString() {
        return super.toString() + "["
            + (discoverTime == 0 ? "" : "discoverTime: " + discoverTime)
            + (finishTime == 0 ? "" : " finishTime: " + finishTime)
            + (predecessor == null ? "" : " predecessor: " + predecessor)
            + (color == null ? "" : " color: " + color)
            + "]";
    }
}
