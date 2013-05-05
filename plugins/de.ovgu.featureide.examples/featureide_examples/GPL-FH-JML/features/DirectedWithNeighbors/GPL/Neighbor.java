package GPL;

import java.util.LinkedList;

// *************************************************************************
   
public class Neighbor implements EdgeIfc, NeighborIfc
{
    public /*@spec_public@*/  Vertex neighbor;
        
    // This constructor has to be present here so that the default one
    // Called on Weighted can call it, i.e. it is not longer implicit    
    public Neighbor( )
    {
        neighbor = null;
    }
    
    public Neighbor( Vertex theNeighbor ) 
    {
        NeighborConstructor( theNeighbor );
    }
    
    public void NeighborConstructor( Vertex theNeighbor ) 
    {
        neighbor = theNeighbor;
    }
  
    public void display () 
    {
        System.out.print( neighbor.name + " ," );
    }

    public /*@pure@*/ Vertex getStart( ) 
    { 
       return null; 
    }

    public /*@pure@*/ Vertex getEnd( ) 
    { 
      return neighbor; 
    }

    public void setWeight( int weight ) 
    {
    }

    public /*@pure@*/ Vertex getOtherVertex( Vertex vertex )
    {
        return neighbor;
    }

    public void adjustAdorns( EdgeIfc the_edge )
    {
    }
}
