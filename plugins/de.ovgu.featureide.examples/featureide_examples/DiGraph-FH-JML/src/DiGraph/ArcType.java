



















  /*@pure@*/  public  class  ArcType  implements JMLType {
	

    //@ public model NodeType from;
    //@ public model NodeType to;
    //@ public invariant from != null && to != null;

    private NodeType _from;

	
    //@                   in from;

    private NodeType _to;

	/*@ 
    //@                 in to;

    //@ private represents from <- _from;
    //@ private represents to <- _to;

    //@ private invariant_redundantly _from != null && _to != null;

     public normal_behavior
     requires from != null && to != null;
     assignable this.from, this.to;
     ensures this.from.equals(from)
          && this.to.equals(to); @*/
	
    
    public ArcType(NodeType from, NodeType to) {
        _from = from;
        _to = to;
    }

	/*@ 

     also @*/ /*@ 
     public normal_behavior
     {|
       requires o instanceof ArcType;
       ensures \result
          <==> ((ArcType)o).from.equals(from)
               && ((ArcType)o).to.equals(to);
     also
       requires !(o instanceof ArcType);
       ensures \result == false;
     |} @*/
	
    
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

	/*@ 

     also @*/ /*@ 
     public normal_behavior
       ensures \result instanceof ArcType
            && (\result).equals(this); @*/
	
    
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
