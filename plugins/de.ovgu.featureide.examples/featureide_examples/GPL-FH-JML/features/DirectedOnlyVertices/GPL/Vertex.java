package GPL;

// dja - trying to fix compile problems
import java.util.Iterator;
import java.util.LinkedList;

// ************************************************************
   
public class Vertex implements EdgeIfc, NeighborIfc
{
    public /*@spec_public@*/ LinkedList adjacentVertices;
    public /*@spec_public@*/ String name;
 
    public Vertex() {
        VertexConstructor();
    }
    /*@ensures name == null && adjacentVertices != null;@*/
    public void VertexConstructor() {
        name      = null;
        adjacentVertices = new LinkedList();
    }
    
    /*@ requires name != null;
    ensures this.name == name;
    ensures \result == this; @*/
    public  Vertex assignName( String name ) {
        this.name = name;
        return ( Vertex ) this;
    }

    //dja: fix for compile errors during performance improvements
    /*@ ensures \result == this.name; @*/
    public /*@pure@*/ String getName( ) 
    { 
        return name; 
    }

    /*@requires n != null;@*/
    /*@ensures adjacentVertices.getLast()==n;@*/
    public void addAdjacent( Vertex n ) {
        adjacentVertices.add( n );
    }

    public void adjustAdorns( Vertex the_vertex, int index ) 
      {}
      
    // dja - trying to fix compile errors
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
            System.out.print( ( ( Vertex )adjacentVertices.get( i ) ).name+", " );
        System.out.println();
    }

//--------------------
// from EdgeIfc
//--------------------

    public Vertex getStart( ) { return null; }
    public Vertex getEnd( ) { return null; }

    public void setWeight( int weight ){}
    public /*@pure@*/  int getWeight() { return 0; }

    //specification enherited
    public /*@pure@*/  Vertex getOtherVertex( Vertex vertex )
    {
        return this;
    }


    //specification enherited
    public void adjustAdorns( EdgeIfc the_edge )
    {
    }

}
