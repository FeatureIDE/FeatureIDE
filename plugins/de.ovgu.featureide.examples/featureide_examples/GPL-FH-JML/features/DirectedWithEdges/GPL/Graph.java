package GPL;

import java.util.LinkedList;
import java.util.Iterator;
import java.util.Collections;
import java.util.Comparator;

// *************************************************************************

public class Graph {
    private /*@spec_public@*/ LinkedList vertices;
    private /*@spec_public@*/ LinkedList edges;
    public /*@spec_public@*/ static final boolean isDirected = true;

    /*@ensures vertices != null && edges != null;@*/
    public Graph() {
        vertices = new LinkedList();
        edges = new LinkedList();
    }

    // Fall back method that stops the execution of programs
    public void run( Vertex s ) {}

    /*@ requires c != null;
    ensures isSorted(edges); @*/
    public void sortEdges(Comparator c) {
        Collections.sort(edges, c);
    }
	/*@public model pure boolean isSorted(LinkedList list) {
 	return true;
 	}@*/
    
    
    
    /*@ requires c != null;
    ensures isSorted(vertices); @*/
    public void sortVertices(Comparator c) {
        Collections.sort(vertices, c);
    }

    // Adds an edge without weights if Weighted layer is not present
	/*@ requires start != null && end != null; @*/
	/*@ ensures \result.getOtherVertex(start)==end && \result.getOtherVertex(end)==start; @*/
    public EdgeIfc addEdge(Vertex start,  Vertex end) {
        Edge theEdge = new  Edge();
        theEdge.EdgeConstructor( start, end );
        edges.add( theEdge );
        start.addNeighbor( new  Neighbor( end, theEdge ) );
        //end.addNeighbor( new  Neighbor( start, theEdge ) );

        return theEdge;
    }

    /*@requires v != null;@*/
    /*@ensures vertices.getLast()==v;@*/
    protected void addVertex( Vertex v ) {
        vertices.add( v );
    }

    // Finds a vertex given its name in the vertices list
    /*@ ensures (theName == null) ==> (\result == null); @*/
    /*@ ensures (\forall int i; i >= 0 && i < vertices.size; (vertices.get(i)!=null) ==> (vertices.get(i).getName().equals(theName) ==> \result != null)); @*/
    /*@ ensures (\result != null) ==> \result.getName() == theName; @*/
    public /*@pure@*/  Vertex findsVertex( String theName )
      {
        Vertex theVertex = null;

        // if we are dealing with the root
        if ( theName==null )
            return null;

        for(VertexIter vxiter = getVertices(); vxiter.hasNext(); )
        {
            theVertex = vxiter.next();
            if ( theName.equals( theVertex.getName() ) )
                return theVertex;
        }

        return theVertex;
    }
    /*@ ensures \result != null; @*/
    public VertexIter getVertices() {
        return new VertexIter() {
                private Iterator iter = vertices.iterator();
                public Vertex next() { return (Vertex)iter.next(); }
                public boolean hasNext() { return iter.hasNext(); }
            };
    }


    public EdgeIter getEdges() {
        return new EdgeIter() {
                private Iterator iter = edges.iterator();
                public EdgeIfc next() { return (EdgeIfc)iter.next(); }
                public boolean hasNext() { return iter.hasNext(); }
            };
    }

    public void display() {
        int i;

        System.out.println( "******************************************" );
        System.out.println( "Vertices " );
        for ( VertexIter vxiter = getVertices(); vxiter.hasNext() ; )
            vxiter.next().display();

        System.out.println( "******************************************" );
        System.out.println( "Edges " );
        for ( EdgeIter edgeiter = getEdges(); edgeiter.hasNext(); )
            edgeiter.next().display();

        System.out.println( "******************************************" );
    }

}
