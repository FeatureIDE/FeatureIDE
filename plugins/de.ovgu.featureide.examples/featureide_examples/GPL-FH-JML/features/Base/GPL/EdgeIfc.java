//created on: Sun Jul 13 23:04:15 CDT 2003

package GPL;

public interface EdgeIfc
{
    public Vertex getStart( );
    public Vertex getEnd( );
    public void display( );


    public void setWeight( int weight );
    
    /*@ requires vertex != null; @*/
	/*@ ensures this.getOtherVertex(\result) == vertex; @*/
	/*@ ensures (\forall Vertex v; Vertex!=null;(this.getOtherVertex(v) != vertex) ==> this.getOtherVertex(vertex) != v); @*/
    public /*@pure@*/ Vertex getOtherVertex( Vertex vertex );
    
    /*@ requires the_edge != null; @*/
    public void adjustAdorns( EdgeIfc the_edge );
}