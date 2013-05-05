





















//@ pure
public  interface  JMLType  extends Cloneable, java.io.Serializable {
	/*@ 

    
     also @*/ /*@ 

        ensures \result != null; @*/
	
      
    public /*@pure@*/ Object clone();

	/*@     

    
     also @*/ /*@ 
       public normal_behavior
         ensures \result ==>
                 ob2 != null; 
     implies_that
       public normal_behavior
       {|
          requires ob2 != null && ob2 instanceof JMLType;
          ensures ((JMLType)ob2).equals(this) == \result;
        also
          requires ob2 == this;
          ensures \result <==> true;
       |} @*/
	
      
    public /*@nullable@*/ boolean equals (Object ob2);


	    

    
    public /*@pure@*/ int hashCode();


}
