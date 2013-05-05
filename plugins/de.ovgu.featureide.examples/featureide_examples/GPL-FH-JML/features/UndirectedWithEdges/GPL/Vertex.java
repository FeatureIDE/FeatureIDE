package GPL;

import java.util.Iterator;
import java.util.LinkedList;

// *********************************************************************

public class Vertex 
{
    public /*@spec_public@*/ LinkedList  neighbors;
    public /*@spec_public@*/ String  name;

    public Vertex( ) 
    {
        VertexConstructor( );
    }
    /*@ensures name == null && adjacentNeighbors != null;@*/
    public void VertexConstructor( ) 
    {
        name      = null;
        neighbors = new LinkedList( );
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
    public String getName( )
    {
        return this.name;
    }

    /*@ ensures \result == this.neighbors;@*/
    public LinkedList getNeighborsObj( )
    {
 	  return neighbors;
    }


    public VertexIter getNeighbors( )
    {
        return new VertexIter( )
        {
            private Iterator iter = neighbors.iterator( );
            public Vertex next( ) 
            { 
              return ( ( Neighbor )iter.next( ) ).end; 
            }
            public boolean hasNext( ) 
            { 
              return iter.hasNext( ); 
            }
        };
    }

    public void display( ) 
    {
        System.out.print( " Node " + name + " connected to: " );

        for ( VertexIter vxiter = getNeighbors( ); vxiter.hasNext( ); )
        {
            System.out.print( vxiter.next().getName() + ", " );
        }

        System.out.println( );
    }      
//--------------------
// differences
//--------------------

    /*@requires n != null;@*/
    /*@ensures neighbors.getLast()==n;@*/
    public void addNeighbor( Neighbor n ) 
    {
        neighbors.add( n );
    }

    public EdgeIter getEdges( )
    {
        return new EdgeIter( )
        {
            private Iterator iter = neighbors.iterator( );
            public EdgeIfc next( ) 
            { 
              return ( ( EdgeIfc ) ( ( Neighbor )iter.next( ) ).edge );
            }
            public boolean hasNext( ) 
            { 
              return iter.hasNext( ); 
            }
        };
    }

}
