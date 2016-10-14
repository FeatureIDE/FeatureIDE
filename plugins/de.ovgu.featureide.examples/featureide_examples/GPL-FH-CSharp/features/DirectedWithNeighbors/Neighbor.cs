/*layer Directed;

import java.util.LinkedList;*/

// *************************************************************************
   
public class Neighbor : EdgeIfc, NeighborIfc
{
    public  Vertex neighbor;
        
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
    
    public virtual void NeighborConstructor( Vertex theNeighbor ) 
    {
        neighbor = theNeighbor;
    }
  
    public virtual void display () 
    {
        System.Console.Out.Write( neighbor.name + " ," );
    }

    public virtual Vertex GetStart( ) 
    { 
       return null; 
    }

    public virtual Vertex GetEnd( ) 
    { 
      return neighbor; 
    }

    public virtual void setWeight( int weight ) 
    {
    }

    public virtual Vertex GetOtherVertex( Vertex vertex )
    {
        return neighbor;
    }

    public virtual void adjustAdorns( EdgeIfc the_edge )
    {
    }
}
