package GPL;

import java.util.LinkedList;
import java.util.Iterator;

  // **********************************************************************   
   
public class Vertex
    {
    public LinkedList adjacentNeighbors;
    public String name;

    public Vertex() 
    {
        VertexConstructor();
    }
      
    /*@ensures name == null && adjacentNeighbors != null;@*/
    public void VertexConstructor() 
    {
        name      = null;
        adjacentNeighbors = new LinkedList();
    }

    /*@ requires name != null;
    ensures this.name == name;
    ensures \result == this; @*/
    public  Vertex assignName( String name ) 
    {
        this.name = name;
        return ( Vertex ) this;
    }
    /*@ ensures \result == this.name; @*/
    public /*@pure@*/  String getName( )
    {
        return this.name;
    }
    
    /*@ ensures \result == this.adjacentNeighbors; @*/
    public /*@pure@*/ LinkedList getNeighborsObj( )
    {
 	  return adjacentNeighbors;
    }

    
    public VertexIter getNeighbors( )
    {
        return new VertexIter( )
        {
            private Iterator iter = adjacentNeighbors.iterator( );
            public Vertex next( ) 
            { 
                return ( ( Neighbor )iter.next( ) ).neighbor; 
            }
            public boolean hasNext( ) 
            { 
                return iter.hasNext( ); 
            }
        };
    }

    public void display( ) 
    {
        System.out.print( "Node " + name + " connected to: " );

        for ( VertexIter vxiter = getNeighbors( ); vxiter.hasNext( ); )
        {
            System.out.print( vxiter.next( ).getName( ) + ", " );
        }

        System.out.println();
    }
//--------------------
// differences
//--------------------

    /*@requires n != null;@*/
    /*@ensures adjacentNeighbors.getLast()==n;@*/ 
    public void addEdge( Neighbor n ) 
    {
        adjacentNeighbors.add( n );
    }

    /*@requires sourceNeighbor != null;
    ensures true;@*/
    public void adjustAdorns( Neighbor sourceNeighbor )
    {
    }

    public EdgeIter getEdges( )
    {
        return new EdgeIter( )
        {
            private Iterator iter = adjacentNeighbors.iterator( );
            public EdgeIfc next( ) 
            { 
                return ( Neighbor ) iter.next( ); 

//              return ( ( EdgeIfc ) ( ( Neighbor )iter.next( ) ).edge );
            }
            public boolean hasNext( ) 
            { 
              return iter.hasNext( ); 
            }
        };
    }


}
