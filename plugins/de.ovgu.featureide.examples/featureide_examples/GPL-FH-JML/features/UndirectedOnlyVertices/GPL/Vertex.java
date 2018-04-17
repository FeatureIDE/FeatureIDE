package GPL;

import java.util.Iterator;
import java.util.LinkedList;

// ************************************************************

public class Vertex implements EdgeIfc, NeighborIfc
{
    public /*@spec_public@*/ LinkedList adjacentVertices;
    public /*@ spec_public@*/ String name;

    public Vertex( )
    {
        VertexConstructor( );
    }
    /*@ensures name == null && adjacentVertices != null;@*/
    /*@assignable name, adjacentVertices; @*/
    public void VertexConstructor( )
    {
        name      = null;
        adjacentVertices = new LinkedList();
    }

    /*@ requires name != null;
    ensures this.name == name;
    ensures \result == this; 
    assignable name; @*/
    public  Vertex assignName( String name )
    {
        this.name = name;
        return ( Vertex ) this;
    }

    public VertexIter getNeighbors( )
    {
        return new VertexIter( )
        {
            private Iterator iter = adjacentVertices.iterator( );
            public Vertex next( )
            {
               return ( Vertex )iter.next( );
            }

            public boolean hasNext( )
            {
               return iter.hasNext( );
            }
        };
    }

    public void display() {
        int s = adjacentVertices.size();
        int i;

        System.out.print( "Vertex " + name + " connected to: " );
        for ( i=0; i<s; i++ )
            System.out.print( ( ( Vertex ) adjacentVertices.get( i ) ).name
                                                + ", " );
        System.out.println();
    }
//--------------------
// differences
//--------------------
    /*@requires n != null;@*/
    /*@ensures adjaventVertices.getLast()==n;@*/
    /*@assignable adjacentVertices; @*/
    public void addAdjacent( Vertex n ) {
        adjacentVertices.add( n );
    }

    public void adjustAdorns( Vertex the_vertex, int index )
      {}
    /*@ensures \result == this.adjacentVertices;@*/
    /*@assignable adjacentVertices; @*/
    public LinkedList getNeighborsObj( )
    {
      return adjacentVertices;
    }

    public EdgeIter getEdges( )
    {
        return new EdgeIter( )
        {
            private Iterator iter = adjacentVertices.iterator( );
            public EdgeIfc next( )
            {
                return ( EdgeIfc ) iter.next( );

//              return ( ( EdgeIfc ) ( ( Neighbor )iter.next( ) ).edge );
            }
            public boolean hasNext( )
            {
              return iter.hasNext( );
            }
        };
    }

    /*@ ensures \result == this.name; @*/
    /*@assignable \nothing; @*/
    public String getName( )
    {
        return this.name;
    }

//--------------------
// from EdgeIfc
//--------------------

    public Vertex getStart( ) { return null; }
    public Vertex getEnd( ) { return null; }

    public void setWeight( int weight ){}
    public int getWeight() { return 0; }

    public Vertex getOtherVertex( Vertex vertex )
    {
        return this;
    }



    public void adjustAdorns( EdgeIfc the_edge )
    {
    }


}
