package GPL;

// dja - trying to fix compile problems
import java.util.Iterator;
import java.util.LinkedList;

// ************************************************************
   
public class Vertex implements EdgeIfc, NeighborIfc
{
    public LinkedList adjacentVertices;
    public String name;
 
    public Vertex() {
        VertexConstructor();
    }
  
    public void VertexConstructor() {
        name      = null;
        adjacentVertices = new LinkedList();
    }

    public  Vertex assignName( String name ) {
        this.name = name;
        return ( Vertex ) this;
    }

    //dja: fix for compile errors during performance improvements
    public String getName( ) 
    { 
        return name; 
    }

 
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
    public int getWeight() { return 0; }

    public Vertex getOtherVertex( Vertex vertex )
    {
        return this;
    }



    public void adjustAdorns( EdgeIfc the_edge )
    {
    }

}
