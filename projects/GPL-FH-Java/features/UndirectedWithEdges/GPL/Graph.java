package GPL;

import java.util.LinkedList;
import java.util.Iterator;
import java.util.Collections;
import java.util.Comparator;

//dja: add for performance reasons
import java.util.HashMap;
import java.util.Map;


// Edge-Neighbor implementation

// *************************************************************************

public class Graph {
    private LinkedList vertices;
    private LinkedList edges;
    public static final boolean isDirected = false;

    //dja: add for performance reasons
    private Map verticesMap;


    public Graph() {
        vertices = new LinkedList();
        edges = new LinkedList();

	  //dja: add for performance reasons
        verticesMap = new HashMap( );

    }

    // Fall back method that stops the execution of programs
    public void run( Vertex s ) {}

    public void sortEdges(Comparator c) {
        Collections.sort(edges, c);
    }

    public void sortVertices(Comparator c) {
        Collections.sort(vertices, c);
    }

    // Adds an edge without weights if Weighted layer is not present
    public EdgeIfc addEdge(Vertex start,  Vertex end) {
        Edge theEdge = new  Edge();
        theEdge.EdgeConstructor( start, end );
        edges.add( theEdge );
        start.addNeighbor( new  Neighbor( end, theEdge ) );
        end.addNeighbor( new  Neighbor( start, theEdge ) );

        return theEdge;
    }

    protected void addVertex( Vertex v ) {
        vertices.add( v );

	  //dja: add for performance reasons
	  verticesMap.put( v.name, v );

    }

    // Finds a vertex given its name in the vertices list
    public  Vertex findsVertex( String theName ) {
        Vertex theVertex;

        // if we are dealing with the root
        if ( theName==null )
            return null;

	  //dja: removed for performance reasons
//        for( VertexIter vxiter = getVertices(); vxiter.hasNext(); )
//        {
//            theVertex = vxiter.next();
//            if ( theName.equals( theVertex.getName() ) )
//                return theVertex;
//        }
//        return null;

	  //dja: add for performance reasons
	  return ( Vertex ) verticesMap.get( theName );

    }


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

    // Finds an Edge given both of its vertices
    public  EdgeIfc findsEdge( Vertex theSource,
                    Vertex theTarget )
       {
        EdgeIfc theEdge;

	  // dja: performance improvement
      //  for( EdgeIter edgeiter = getEdges(); edgeiter.hasNext(); )
        for( EdgeIter edgeiter = theSource.getEdges(); edgeiter.hasNext(); )
         {
            theEdge = edgeiter.next();
            if ( ( theEdge.getStart().getName().equals( theSource.getName() ) &&
                  theEdge.getEnd().getName().equals( theTarget.getName() ) ) ||
                 ( theEdge.getStart().getName().equals( theTarget.getName() ) &&
                  theEdge.getEnd().getName().equals( theSource.getName() ) ) )
                return theEdge;
        }
        return null;
    }

    public void display() {
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
