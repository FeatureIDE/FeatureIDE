



















  /*@nullable_by_default@*/  
public  class  TransposableNode  extends ValueNode {
	/*@ 

     public normal_behavior
       assignable value;
       ensures value == v; @*/
	            
      
    public TransposableNode(Object v) {
        setValue(v);
    }

	/*@ 

     also @*/ /*@ 
       public normal_behavior
         requires o instanceof TransposableNode;
         ensures \result
             ==> JMLNullSafe.equals(value, ((TransposableNode)o).value);
     also
       public normal_behavior
         requires !(o instanceof TransposableNode);
         ensures \result == false; @*/
	
      
    public boolean equals( /*@nullable@*/ Object o) {
        return (o instanceof TransposableNode)
            && super.equals(o);
    }


	

    protected /*@pure@*/ /*@non_null@*/ String className() {
        return "TransposableNode";
    }


}
