package GPL;

import java.util.Iterator;
import java.util.LinkedList;

// *********************************************************************

public class Vertex 
{
    public LinkedList neighbors;
    public String name;

    public Vertex( ) 
    {
        VertexConstructor( );
    }

    public void VertexConstructor( ) 
    {
        name      = null;
        neighbors = new LinkedList( );
    }

    public  Vertex assignName( String name ) 
    {
        this.name = name;
        return ( Vertex ) this;
    }

    public String getName( )
    {
        return this.name;
    }

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
