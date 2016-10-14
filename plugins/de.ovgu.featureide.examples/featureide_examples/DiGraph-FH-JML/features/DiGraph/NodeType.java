// @(#)$Id: NodeType.java 1199 2009-02-17 19:42:32Z smshaner $

// Copyright (C) 1998, 1999, 2003 Iowa State University

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

public /*@pure@*/ interface NodeType extends JMLType {
  
  /*@ also
    @   public normal_behavior
    @       requires !(o instanceof NodeType);
    @       ensures \result == false;
    @*/
  public boolean equals( /*@nullable@*/ Object o);

  public int hashCode();

  /*@ also
    @   public normal_behavior
    @     ensures \result instanceof NodeType
    @          && (\result).equals(this);
    @*/
  public Object clone();

}
