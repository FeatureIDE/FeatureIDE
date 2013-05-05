package GPL;

import java.util.LinkedList;

// Vertex class

 // *************************************************************************

public class Neighbor implements EdgeIfc, NeighborIfc
{
    public /*@spec_public@*/  Vertex neighbor;

    // This constructor has to be present here so that the default one
    // Called on Weighted can call it, i.e. it is not longer implicit
    /*@ensures  neighbor == null;@*/
    public Neighbor()  {
        neighbor = null;
    }
    
    /*@ensures this.neighbor == theNeighbor;@*/ 
    public Neighbor( Vertex theNeighbor )
   {
        NeighborConstructor( theNeighbor );
    }

    public void setWeight(int weight) {}
    public int getWeight() { return 0; }

    public void NeighborConstructor( Vertex theNeighbor ) {
        neighbor = theNeighbor;
    }

    public void display()
    {
        System.out.print( neighbor.name + " ," );
    }

    public /*@pure@*/ Vertex getStart( ) { return null; }
    public /*@pure@*/ Vertex getEnd( ) { return null; }

    /*@ensures \result == neighbor;@*/
    public /*@pure@*/ Vertex getOtherVertex( Vertex vertex )
    {
        return neighbor;
    }

    public void adjustAdorns( EdgeIfc the_edge )
    {
    }
}
