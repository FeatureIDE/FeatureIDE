//layer Undirected;

using System.Collections;
using System.Collections.Generic;
//import java.util.Iterator;
//import java.util.Collections;
//import java.util.Comparator;

//dja: Add for performance reasons
//import java.util.HashMap;
//import java.util.Map;


// Edge-Neighbor implementation

// *************************************************************************

public class Graph {
    private List<Vertex> vertices;
    private List<EdgeIfc> edges;
    public static readonly bool isDirected = false;

    //dja: Add for performance reasons
    private Dictionary<string, Vertex> verticesMap;


    public Graph() {
        vertices = new List<Vertex>();
        edges = new List<EdgeIfc>();

	  //dja: Add for performance reasons
        verticesMap = new Dictionary<string, Vertex>( );

    }

    // Fall back method that stops the execution of programs
    public void run( Vertex s ) {}

    public void sortEdges(System.Collections.Generic.IComparer<EdgeIfc> c) {
        edges.Sort(c);
    }

    public void sortVertices(System.Collections.Generic.IComparer<Vertex> c) {
        vertices.Sort(c);
    }

    // Adds an edge without weights if Weighted layer is not present
    public EdgeIfc AddEdge(Vertex start,  Vertex end) {
        Edge theEdge = new  Edge();
        theEdge.EdgeConstructor( start, end );
        edges.Add( theEdge );
        start.AddNeighbor( new  Neighbor( end, theEdge ) );
        end.AddNeighbor( new  Neighbor( start, theEdge ) );

        return theEdge;
    }

    public void AddVertex( Vertex v ) {
        vertices.Add( v );

	  //dja: Add for performance reasons
	  verticesMap.Add( v.name, v );

    }

    // Finds a vertex given its name in the vertices list
    public  Vertex findsVertex( string theName ) {
        Vertex theVertex;

        // if we are dealing with the root
        if ( theName==null )
            return null;

	  //dja: Removed for performance reasons
//        for( Iterator<Vertex> vxiter = GetVertices(); vxiter.hasNext(); )
//        {
//            theVertex = vxiter.next();
//            if ( theName.Equals( theVertex.GetName() ) )
//                return theVertex;
//        }
//        return null;

	  //dja: Add for performance reasons
        return (Vertex)verticesMap[theName];

    }


    public Iterator<Vertex> GetVertices() {
        return new Iterator<Vertex>(vertices.GetEnumerator());
    }
    public Iterator<EdgeIfc> GetEdges() {
        return new Iterator<EdgeIfc>(edges.GetEnumerator());
    }
    // Finds an Edge given both of its vertices
    public  EdgeIfc findsEdge( Vertex theSource,
                    Vertex theTarGet )
       {
        EdgeIfc theEdge;

	  // dja: performance improvement
      //  for( Iterator<EdgeIfc> edgeiter = GetEdges(); edgeiter.hasNext(); )
        for( Iterator<EdgeIfc> edgeiter = theSource.GetEdges(); edgeiter.hasNext(); )
         {
            theEdge = edgeiter.next();
            if ( ( theEdge.GetStart().GetName().Equals( theSource.GetName() ) &&
                  theEdge.GetEnd().GetName().Equals( theTarGet.GetName() ) ) ||
                 ( theEdge.GetStart().GetName().Equals( theTarGet.GetName() ) &&
                  theEdge.GetEnd().GetName().Equals( theSource.GetName() ) ) )
                return theEdge;
        }
        return null;
    }

    public void display() {
        System.Console.Out.WriteLine( "******************************************" );
        System.Console.Out.WriteLine( "Vertices " );
        for ( Iterator<Vertex> vxiter = GetVertices(); vxiter.hasNext() ; )
            vxiter.next().display();

        System.Console.Out.WriteLine( "******************************************" );
        System.Console.Out.WriteLine( "Edges " );
        for ( Iterator<EdgeIfc> edgeiter = GetEdges(); edgeiter.hasNext(); )
            edgeiter.next().display();

        System.Console.Out.WriteLine( "******************************************" );
    }
}
