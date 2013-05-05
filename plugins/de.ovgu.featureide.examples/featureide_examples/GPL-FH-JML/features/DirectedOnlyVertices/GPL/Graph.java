package GPL;

//dja - trying to fix logic problems
import java.util.Iterator;
import java.util.LinkedList;
//dja: added to fix compile problems when doing the performance improvements
import java.util.Comparator;
import java.util.Collections;


// ************************************************************

public class Graph {
	public /*@ spec_public @*/  LinkedList vertices;
    public /*@spec_public@*/ static final boolean isDirected = true;

    public Graph() {
        vertices = new LinkedList();
    }
    /*@ ensures \result != null; @*/
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
    
    //TODO: remove cloned model 
	/*@public model pure boolean isSorted(LinkedList list) {
 	return true;
 	}@*/

    
    /*@ requires c != null;
    ensures isSorted(vertices); @*/
    public void sortVertices(Comparator c) {
        Collections.sort(vertices, c);
    }

    // Adds an edge without weights if Weighted layer is not present
    /*@requires start != null && end != null; @*/
    /*@ ensures \result.getOtherVertex(v1)==v2 && \result.getOtherVertex(v2)==v1; @*/
    public void addAnEdge( Vertex start,  Vertex end, int weight )
      {
        addEdge( start,end );
    }


    /*@requires v != null;@*/
    /*@ensures vertices.getLast()==v;@*/
    public void addVertex( Vertex v ) {
        vertices.add( v );
    }

    // Adds and edge by setting end as adjacent to start vertices
	/*@ requires v1 != null && v2 != null; @*/
	/*@ ensures \result.getOtherVertex(v1)==v2 && \result.getOtherVertex(v2)==v1; @*/
    public EdgeIfc addEdge( Vertex start,  Vertex end ) {
        start.addAdjacent( end );
        return( EdgeIfc ) start;
    }

    // Finds a vertex given its name in the vertices list
    // ensures \null cannot be used because it is not clear whether null 
    /*@ ensures (theName == null) ==> (\result == null); @*/
    /*@ ensures (\forall int i; i >= 0 && i < vertices.size; (vertices.get(i)!=null) ==> (vertices.get(i).getName().equals(theName) ==> \result != null)); @*/
    /*@ ensures (\result != null) ==> \result.getName() == theName; @*/
        public /*@pure@*/ Vertex findsVertex( String theName )
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
