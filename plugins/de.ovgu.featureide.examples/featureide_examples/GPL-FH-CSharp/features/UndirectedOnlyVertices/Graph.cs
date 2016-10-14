//layer Undirected;

//import java.util.Iterator;
using System.Collections;
using System.Collections.Generic;

//dja: Add for performance reasons
//import java.util.HashMap;
//import java.util.Map;

// ************************************************************

public class Graph
{
    public List<Vertex> vertices;
    public static readonly bool isDirected = false;
    //dja: Add for performance reasons
    private Dictionary<string, Vertex> verticesMap;


    public Graph( )
    {
        vertices = new List<Vertex>();
	  //dja: Add for performance reasons
        verticesMap = new Dictionary<string, Vertex>( );

    }

    // Fall back method that stops the execution of programs
    public void run( Vertex s )
    {
    }

    // Adds an edge without weights if Weighted layer is not present
    public void AddAnEdge( Vertex start,  Vertex end, int weight )
    {
        AddEdge( start,end );
    }

    // Adds and edge by setting start as adjacent to end and
    // viceversa
    public EdgeIfc AddEdge( Vertex start,  Vertex end )
    {
        start.AddAdjacent( end );
        end.AddAdjacent( start );
        return ( EdgeIfc ) start;
    }

     // Adds an edge without weights if Weighted layer is not present
 //   public void AddEdge( Vertex start,   NeighborIfc theNeighbor )
   // {
     //   AddEdge( Vertex start,  ( Vertex ) theNeighbor )
   // }



    public void AddVertex( Vertex v )
    {
        vertices.Add( v );

	  //dja: Add for performance reasons
	  verticesMap.Add( v.name, v );
    }

    // Finds a vertex given its name in the vertices list
    public  Vertex findsVertex( string theName )
      {
        int i=0;
        Vertex theVertex;

        // if we are dealing with the root
        if ( theName == null )
            return null;

	  //dja: Removed for performance reasons
//        for( i=0; i<vertices.Count; i++ )
//        {
//            theVertex = ( Vertex )vertices.Get( i );
//            if ( theName.Equals( theVertex.name ) )
//                return theVertex;
//        }
//        return null;

	  //dja: Add for performance reasons
        return (Vertex)verticesMap[theName];
    }

    public Iterator<Vertex> GetVertices( ) {
        return new Iterator<Vertex>(vertices.GetEnumerator() );
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
   public  EdgeIfc findsEdge( Vertex theSource,
                    Vertex theTarGet )
       {
        //dja: performance improvement
//        for( Iterator<Vertex> vertexiter = GetVertices(); vertexiter.hasNext(); )
//         {
//        Vertex v1 = vertexiter.next( );
//        for( EdgeIter edgeiter = v1.GetEdges(); edgeiter.hasNext(); )
//            {
//                EdgeIfc theEdge = edgeiter.next();
//            Vertex v2 = theEdge.GetOtherVertex( v1 );
//              if ( ( v1.GetName().Equals( theSource.GetName() ) &&
//                       v2.GetName().Equals( theTarGet.GetName() ) ) ||
//                         ( v1.GetName().Equals( theTarGet.GetName() ) &&
//                     v2.GetName().Equals( theSource.GetName() ) ) )
//                    return theEdge;
//            }
//        }
        Vertex v1 = theSource;
        for( Iterator<EdgeIfc> edgeiter = v1.GetEdges(); edgeiter.hasNext(); )
            {
                EdgeIfc theEdge = edgeiter.next();
            Vertex v2 = theEdge.GetOtherVertex( v1 );
              if ( ( v1.GetName().Equals( theSource.GetName() ) &&
                       v2.GetName().Equals( theTarGet.GetName() ) ) ||
                         ( v1.GetName().Equals( theTarGet.GetName() ) &&
                     v2.GetName().Equals( theSource.GetName() ) ) )
                    return theEdge;
            }
        return null;
    }

}
