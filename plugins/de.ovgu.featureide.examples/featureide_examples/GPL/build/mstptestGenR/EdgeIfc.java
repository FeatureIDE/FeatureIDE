//created on: Sun Jul 13 23:04:15 CDT 2003

package mstptestGenR;



abstract interface EdgeIfc$$Base
{
    public Vertex getStart( );
    public Vertex getEnd( );
    public void display( );

    public Vertex getOtherVertex( Vertex vertex );
    public void adjustAdorns( EdgeIfc the_edge );
}

//created on: Sat Dec 04 11:42:44 CST 2004

public interface EdgeIfc extends EdgeIfc$$Base
{
    public void setWeight( int weight );
    public int getWeight();
}