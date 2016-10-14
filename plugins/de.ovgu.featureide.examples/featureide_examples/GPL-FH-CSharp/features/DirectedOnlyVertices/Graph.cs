//layer Directed;

//dja - trying to fix logic problems
//import java.util.Iterator;
using System.Collections;
using System.Collections.Generic;
//dja: Added to fix compile problems when doing the performance improvements
//import java.util.Comparator;
//import java.util.Collections;


// ************************************************************

public class Graph {
    public List<Vertex> vertices;
    public static readonly bool isDirected = true;

    public Graph() {
        vertices = new List<Vertex>();
    }

    public Iterator<Vertex> GetVertices( ) { 
        // dja - trying to fix logic problems
        return new Iterator<Vertex>(vertices.GetEnumerator());
        //return new VertexIterInternal(vertices.GetEnumerator() );
    }
// dja - fix compile code.
//    public Iterator<EdgeIfc> GetEdges() { return null; }
//    public EdgeIfc AddEdge(Vertex start,  Vertex end) { return null; }
//    public  Vertex findsVertex( string theName ) { return null; }

    // Fall back method that stops the execution of programs
    public void run( Vertex s ) {}

    //dja: fix for compile problems during performance improvements
    public void sortVertices(System.Collections.Generic.IComparer<Vertex> c) {
        vertices.Sort(c);
    }

    // Adds an edge without weights if Weighted layer is not present
    public void AddAnEdge( Vertex start,  Vertex end, int weight )
      {
        AddEdge( start,end );
    }



    public void AddVertex( Vertex v ) {
        vertices.Add( v );
    }

    // Adds and edge by setting end as adjacent to start vertices
    public EdgeIfc AddEdge( Vertex start,  Vertex end ) {
        start.AddAdjacent( end );
        return start;
    }

    // Finds a vertex given its name in the vertices list
    public  Vertex findsVertex( string theName )
      {
        int i=0;
        Vertex theVertex;

        // if we are dealing with the root
        if ( theName==null )
            return null;

        for( i=0; i<vertices.Count; i++ )
            {
            theVertex = vertices[i];
            if ( theName.Equals( theVertex.name ) )
                return theVertex;
        }
        return null;
    }

    public void display() {
        int s = vertices.Count;
        int i;

        System.Console.Out.WriteLine( "******************************************" );
        System.Console.Out.WriteLine( "Vertices " );
        for ( i=0; i<s; i++ )
            ( ( Vertex ) vertices[i] ).display();
        System.Console.Out.WriteLine( "******************************************" );

    }
}
