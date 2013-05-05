


















public  class  Arc  implements Cloneable {
	

    private  /*@spec_public@*/ /*@non_null@*/  NodeType source;

	
    private  /*@spec_public@*/ /*@non_null@*/  NodeType target;

	/*@ 
    
    //@ private invariant_redundantly source != null && target != null;

    
     public normal_behavior
       requires_redundantly source != null && target != null;
       assignable this.source, this.target;
       ensures this.source == source
            && this.target == target; @*/
	
      
    public Arc(NodeType source, NodeType target) {
        this.source = source;
        this.target = target;
    }

	/*@ 

     also @*/ /*@ 
       public normal_behavior
         requires o instanceof Arc;
         ensures \result
                 ==> ((Arc)o).source.equals(this.source)
                     && ((Arc)o).target.equals(this.target);
     also
       public normal_behavior
         requires !(o instanceof Arc);
         ensures \result == false; @*/
	
      
    public /*@pure@*/ boolean equals (Object o) {
        return (o instanceof Arc) 
            && ((Arc)o).source.equals(source)
            && ((Arc)o).target.equals(target);
    }

	/*@ 

     also @*/ /*@ 
       public normal_behavior
         ensures \result instanceof Arc
             && (\result).equals(this); @*/
	
      
    public /*@pure@*/ Object clone() {
        Arc res;
        try {
            res = (Arc)super.clone();
        } catch (CloneNotSupportedException e) {
            
            throw new InternalError(e.getMessage());
        }
	
	
	//@ assume res.source == source && res.target == target;
	return res;
    }


	
    
    public /*@pure@*/ int hashCode() {
        return source.hashCode() + target.hashCode();
    }

	/*@ 

    
     public normal_behavior
       assignable source, target;
       ensures source == \old(target) && target == \old(source); @*/
	
      
    public void flip() {
        NodeType temp = source;
        source = target;
        target = temp;
    }

	/*@ 

    
     public normal_behavior
       assignable \nothing;
       ensures \result == source; @*/
	           
      
    public /*@pure@*/ NodeType getSource() {
        return source;
    }

	/*@ 

    
     public normal_behavior
       requires_redundantly source != null;
       assignable this.source;
       ensures this.source == source; @*/
	           
      
    public void setSource(NodeType source) {
        this.source = source;
    }

	/*@ 

    
     public normal_behavior
       assignable \nothing;
       ensures \result == target; @*/
	           
      
    public /*@pure@*/ NodeType getTarget() {
        return target;
    }

	/*@ 

    
     public normal_behavior
       requires_redundantly target != null;
       assignable this.target;
       ensures this.target == target; @*/
	           
      
    public void setTarget(NodeType target) {
        this.target = target;
    }


	

    
    //@ ensures \result != null;
    protected /*@pure@*/ String className() {
        return "Arc";
    }


	

    public String toString() {
        return className() + "[from: " + source + ", to: " + target + "]";
    }


}
