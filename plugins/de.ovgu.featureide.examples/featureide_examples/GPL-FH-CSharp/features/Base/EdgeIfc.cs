/*
 * //created on: Sun Jul 13 23:04:15 CDT 2003

layer base;
*/
public interface EdgeIfc
{
    Vertex GetStart( );
    Vertex GetEnd( );
    void display( );


    void setWeight( int weight );
 //   public int GetWeight();

    Vertex GetOtherVertex( Vertex vertex );

    void adjustAdorns( EdgeIfc the_edge );
}