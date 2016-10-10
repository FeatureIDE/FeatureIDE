//layer Undirected;

//import java.util.Iterator;
using System.Collections;
using System.Collections.Generic;

//dja: Add for performance reasons
//import java.util.HashMap;
//import java.util.Map;


// *************************************************************************
   
public class Graph 
{
    public List<Vertex> vertices;
    public static bool isDirected = false;
      
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
    public void AddEdge( Vertex start,   Neighbor theNeighbor ) 
    {
        start.AddEdge( theNeighbor );
        Vertex end = theNeighbor.neighbor;
        end.AddEdge( new  Neighbor( start ) );
    }

        
    public void AddVertex( Vertex v ) 
    {
        vertices.Add( v );

	  //dja: Add for performance reasons
	  verticesMap.Add( v.name, v );
    }
   
    // Finds a vertex given its name in the vertices list
    public  Vertex findsVertex( string theName )
    {
        Vertex theVertex;
        
        // if we are dealing with the root
        if ( theName == null )
            return null;

	  //dja: Removed for performance reasons
//        for( VertexIter vxiter = GetVertices( ); vxiter.hasNext( ); )
//        {
//            theVertex = vxiter.next( );
//            if ( theName.Equals( theVertex.GetName( ) ) )
//            {
//               return theVertex;
//            }
//        }
//        return null;

	  //dja: Add for performance reasons
        return (Vertex)verticesMap[theName];

    }

    public Iterator<Vertex> GetVertices( ) {
        return new Iterator<Vertex>(vertices.GetEnumerator());
    }

    // Finds an Edge given both of its vertices
    public  EdgeIfc findsEdge( Vertex theSource,
                    Vertex theTarGet )
       {
	  //dja: performance improvement
        //for( VertexIter vertexiter = GetVertices(); vertexiter.hasNext(); )
        // {
	  //	Vertex v1 = vertexiter.next( );
	  //	for( EdgeIter edgeiter = v1.GetEdges(); edgeiter.hasNext(); )
        //    {
	  //          EdgeIfc theEdge = edgeiter.next();
	  //		Vertex v2 = theEdge.GetOtherVertex( v1 );
        //	      if ( ( v1.GetName().Equals( theSource.GetName() ) &&
        //    	       v2.GetName().Equals( theTarGet.GetName() ) ) ||
        //         	     ( v1.GetName().Equals( theTarGet.GetName() ) &&
        //          	 v2.GetName().Equals( theSource.GetName() ) ) )
        //        	return theEdge;
        //    }
        //}
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


    public void display( ) 
    {
        System.Console.Out.WriteLine( "******************************************" );
        System.Console.Out.WriteLine( "Vertices " );
        for ( Iterator<Vertex> vxiter = GetVertices( ); vxiter.hasNext( ) ; )
        {
            vxiter.next( ).display( );
        }

        System.Console.Out.WriteLine( "******************************************" );
    }

    // Adds an edge without weights if Weighted layer is not present
    public EdgeIfc AddEdge( Vertex start,  Vertex end )
      {
	  Neighbor e = new Neighbor( end );
        AddEdge( start, e );
        return e;
    }
      
}
