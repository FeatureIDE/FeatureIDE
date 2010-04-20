package GPL;

//dja - trying to fix logic problems
import java.util.Iterator;
import java.util.LinkedList;
//dja: added to fix compile problems when doing the performance improvements
import java.util.Comparator;
import java.util.Collections;


// ************************************************************

public class Graph {
    public LinkedList vertices;
    public static final boolean isDirected = true;

    public Graph() {
        vertices = new LinkedList();
    }

    public VertexIter getVertices( ) 
    { 
        // dja - trying to fix logic problems
        return new VertexIter( ) 
        {
                private Iterator iter = vertices.iterator( );
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
// dja - fix compile code.
//    public EdgeIter getEdges() { return null; }
//    public EdgeIfc addEdge(Vertex start,  Vertex end) { return null; }
//    public  Vertex findsVertex( String theName ) { return null; }

    // Fall back method that stops the execution of programs
    public void run( Vertex s ) {}

    //dja: fix for compile problems during performance improvements
    public void sortVertices(Comparator c) {
        Collections.sort(vertices, c);
    }

    // Adds an edge without weights if Weighted layer is not present
    public void addAnEdge( Vertex start,  Vertex end, int weight )
      {
        addEdge( start,end );
    }



    public void addVertex( Vertex v ) {
        vertices.add( v );
    }

    // Adds and edge by setting end as adjacent to start vertices
    public EdgeIfc addEdge( Vertex start,  Vertex end ) {
        start.addAdjacent( end );
        return( EdgeIfc ) start;
    }

    // Finds a vertex given its name in the vertices list
    public  Vertex findsVertex( String theName )
      {
        int i=0;
        Vertex theVertex;

        // if we are dealing with the root
        if ( theName==null )
            return null;

        for( i=0; i<vertices.size(); i++ )
            {
            theVertex = ( Vertex )vertices.get( i );
            if ( theName.equals( theVertex.name ) )
                return theVertex;
        }
        return null;
    }

    public void display() {
        int s = vertices.size();
        int i;

        System.out.println( "******************************************" );
        System.out.println( "Vertices " );
        for ( i=0; i<s; i++ )
            ( ( Vertex ) vertices.get( i ) ).display();
        System.out.println( "******************************************" );

    }
}
