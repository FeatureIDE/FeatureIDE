//layer Directed;

using System.Collections;
using System.Collections.Generic;
//import java.util.Iterator;
//import java.util.Collections;
//import java.util.Comparator;

// *************************************************************************

public class Graph {
    private List<Vertex> vertices;
    private List<EdgeIfc> edges;
    public static readonly bool isDirected = true;

    public Graph() {
        vertices = new List<Vertex>();
        edges = new List<EdgeIfc>();
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
        //end.AddNeighbor( new  Neighbor( start, theEdge ) );

        return theEdge;
    }

    public void AddVertex( Vertex v ) {
        vertices.Add( v );
    }

    // Finds a vertex given its name in the vertices list
    public  Vertex findsVertex( string theName )
      {
        Vertex theVertex = null;

        // if we are dealing with the root
        if ( theName==null )
            return null;

        for(Iterator<Vertex> vxiter = GetVertices(); vxiter.hasNext(); )
        {
            theVertex = vxiter.next();
            if ( theName.Equals( theVertex.GetName() ) )
                return theVertex;
        }

        return theVertex;
    }

    public Iterator<Vertex> GetVertices() {
        return new Iterator<Vertex>(vertices.GetEnumerator());
    }
    public Iterator<EdgeIfc> GetEdges() {
        return new Iterator<EdgeIfc>(edges.GetEnumerator());
    }
    public void display() {
        int i;

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
