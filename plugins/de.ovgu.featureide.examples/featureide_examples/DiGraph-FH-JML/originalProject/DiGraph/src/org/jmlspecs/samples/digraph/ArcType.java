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


package org.jmlspecs.samples.digraph;

//@ refine "ArcType.jml";

import org.jmlspecs.models.JMLType;

/*@ pure */ public class ArcType implements JMLType {

    private NodeType _from;
    //@                   in from;

    private NodeType _to;
    //@                 in to;

    //@ private represents from <- _from;
    //@ private represents to <- _to;

    //@ private invariant_redundantly _from != null && _to != null;

    public ArcType(NodeType from, NodeType to) {
        _from = from;
        _to = to;
    }

    public boolean equals(/*@nullable@*/ Object o) {
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
