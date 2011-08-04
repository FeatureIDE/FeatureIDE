//layer Undirected;

using System.Collections;

// Vertex class

 // *************************************************************************

public class Neighbor : EdgeIfc, NeighborIfc
{
    public  Vertex neighbor;

    // This constructor has to be present here so that the default one
    // Called on Weighted can call it, i.e. it is not longer implicit
    public Neighbor()  {
        neighbor = null;
    }

    public Neighbor( Vertex theNeighbor )
   {
        NeighborConstructor( theNeighbor );
    }

    public void setWeight(int weight) {}
    public int GetWeight() { return 0; }

    public void NeighborConstructor( Vertex theNeighbor ) {
        neighbor = theNeighbor;
    }

    public void display()
    {
        System.Console.Out.Write( neighbor.name + " ," );
    }

    public Vertex GetStart( ) { return null; }
    public Vertex GetEnd( ) { return null; }

    public Vertex GetOtherVertex( Vertex vertex )
    {
        return neighbor;
    }

    public void adjustAdorns( EdgeIfc the_edge )
    {
    }
}
