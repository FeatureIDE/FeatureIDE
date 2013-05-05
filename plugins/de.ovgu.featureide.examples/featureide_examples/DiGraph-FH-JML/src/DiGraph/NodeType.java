



















public /*@pure@*/   interface  NodeType  extends JMLType {
	/*@ 
  
   also @*/ /*@ 
     public normal_behavior
         requires !(o instanceof NodeType);
         ensures \result == false; @*/
	
    
  public boolean equals( /*@nullable@*/ Object o);


	

  public int hashCode();

	/*@ 

   also @*/ /*@ 
     public normal_behavior
       ensures \result instanceof NodeType
            && (\result).equals(this); @*/
	
    
  public Object clone();


}
