/*layer Directed;

import java.util.Iterator;
import java.util.LinkedList;
//dja: Added to fix compile problems when doing the performance improvements
import java.util.Comparator;
import java.util.Collections;*/

// Neighbor implementation
   
// *************************************************************************
   using System.Collections;
   using System.Collections.Generic;
public class Graph {
    public List<Vertex> vertices;
    public static bool isDirected = true;

    public Graph() {
        vertices = new List<Vertex>();
    }
 
    // Fall back method that stops the execution of programs
    public virtual void run( Vertex s )
      { }

    //dja: fix for compile problems during performance improvements
    public virtual void sortVertices(System.Collections.Generic.IComparer<Vertex> c) {
        vertices.Sort(c);
    }


    // Adds an edge without weights if Weighted layer is not present
//    public virtual void AddAnEdge( Vertex start,  Vertex end, int weight )
  //    {
    //    AddEdge( start, new  Neighbor( end ) );
//    }

    // Adds an edge without weights if Weighted layer is not present
    public virtual EdgeIfc AddEdge( Vertex start,  Vertex end )
    {
	  Neighbor e = new Neighbor( end );
        AddEdge( start, e );
        return e;
    }

        
    public virtual void AddVertex( Vertex v ) {
        vertices.Add( v );
    }
   
    public virtual void AddEdge( Vertex start,  Neighbor theNeighbor ) {
        start.AddEdge( theNeighbor );
    }
    
    // Finds a vertex given its name in the vertices list
    public  virtual Vertex findsVertex( string theName )
      {
        Vertex theVertex = null;

        // if we are dealing with the root
        if ( theName==null )
        {
            return null;
        }

        for(Iterator<Vertex> vxiter = GetVertices( ); vxiter.hasNext( ); )
        {
            theVertex = vxiter.next( );
            if ( theName.Equals( theVertex.GetName( ) ) )
            {
                return theVertex;
            }
        }

        return theVertex;
    }

    public virtual Iterator<Vertex> GetVertices() {
        return new Iterator<Vertex>(vertices.GetEnumerator());
    }
    public virtual void display( ) 
    {
        System.Console.Out.WriteLine( "******************************************" );
        System.Console.Out.WriteLine( "Vertices " );
        for ( Iterator<Vertex> vxiter = GetVertices( ); vxiter.hasNext( ) ; )
        {
            vxiter.next( ).display( );
        }
        System.Console.Out.WriteLine( "******************************************" );

    }
      
}
