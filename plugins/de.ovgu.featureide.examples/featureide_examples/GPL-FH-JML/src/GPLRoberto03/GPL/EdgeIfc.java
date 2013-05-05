

package GPL; 

public   interface  EdgeIfc {

	
    
    public /*@pure@*/ int getWeight();


	
    public Vertex getStart( );


	
    public Vertex getEnd( );


	
    public void display( );


	


    public void setWeight( int weight );

	/*@ 
    
     requires vertex != null; 
	 ensures this.getOtherVertex(\result) == vertex; 
	 ensures (\forall Vertex v; Vertex!=null;(this.getOtherVertex(v) != vertex) ==> this.getOtherVertex(vertex) != v); @*/
	 
    public /*@pure@*/ Vertex getOtherVertex( Vertex vertex );

	/*@ 
    
     requires the_edge != null; @*/
	 
    public void adjustAdorns( EdgeIfc the_edge );


}
