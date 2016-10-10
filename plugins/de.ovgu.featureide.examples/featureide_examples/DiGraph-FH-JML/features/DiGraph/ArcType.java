// @(#)$Id: ArcType.java 1199 2009-02-17 19:42:32Z smshaner $

// Copyright (C) 1998, 1999 Iowa State University

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

/*@ pure */ public class ArcType implements JMLType {

    //@ public model NodeType from;
    //@ public model NodeType to;
    //@ public invariant from != null && to != null;

    private NodeType _from;
    //@                   in from;

    private NodeType _to;
    //@                 in to;

    //@ private represents from <- _from;
    //@ private represents to <- _to;

    //@ private invariant_redundantly _from != null && _to != null;

    /*@ public normal_behavior
    @   requires from != null && to != null;
    @   assignable this.from, this.to;
    @   ensures this.from.equals(from)
    @        && this.to.equals(to);
    @*/
    public ArcType(NodeType from, NodeType to) {
        _from = from;
        _to = to;
    }

    /*@ also
    @   public normal_behavior
    @   {|
    @     requires o instanceof ArcType;
    @     ensures \result
    @        <==> ((ArcType)o).from.equals(from)
    @             && ((ArcType)o).to.equals(to);
    @   also
    @     requires !(o instanceof ArcType);
    @     ensures \result == false;
    @   |}
    @*/
    public boolean equals( /*@nullable@*/ Object o) {
        return o instanceof ArcType
            && ((ArcType)o)._from.equals(_from)
            && ((ArcType)o)._to.equals(_to);
    }

    public int hashCode() {
        return _from.hashCode() + _to.hashCode();
    }

    //@ ensures \result == from;
    public NodeType getFrom() {
        return _from;
    }

    //@ ensures \result == to;
    public NodeType getTo() {
        return _to;
    }

    /*@ also
    @   public normal_behavior
    @     ensures \result instanceof ArcType
    @          && (\result).equals(this);
    @*/
    public Object clone() {
        return new ArcType(_from, _to);
    }

    protected String className() {
        return "ArcType";
    }

    public String toString() {
        return className() + "[from: " + _from + ", to: " + _to + "]";
    }
}
