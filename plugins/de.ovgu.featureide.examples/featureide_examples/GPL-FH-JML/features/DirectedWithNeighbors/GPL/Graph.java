package GPL;

import java.util.Iterator;
import java.util.LinkedList;
//dja: added to fix compile problems when doing the performance improvements
import java.util.Comparator;
import java.util.Collections;

// Neighbor implementation
   
// *************************************************************************
   
public class Graph {
    public LinkedList vertices;
    public static boolean isDirected = true;

    public Graph() {
        vertices = new LinkedList();
    }
 
    // Fall back method that stops the execution of programs
    public void run( Vertex s )
      { }

    //dja: fix for compile problems during performance improvements
	/*@public model pure boolean isSorted(LinkedList list) {
 	return true;
 	}@*/
    /*@ requires c != null;
    ensures isSorted(vertices); 
    assignable vertices;@*/
    public void sortVertices(Comparator c) {
        Collections.sort(vertices, c);
    }


    // Adds an edge without weights if Weighted layer is not present
//    public void addAnEdge( Vertex start,  Vertex end, int weight )
  //    {
    //    addEdge( start, new  Neighbor( end ) );
//    }

    // Adds an edge without weights if Weighted layer is not present
	/*@ requires v1 != null && v2 != null; @*/
	/*@ ensures \result.getOtherVertex(v1)==v2 && \result.getOtherVertex(v2)==v1; @*/
    /*@assignable \nothing; @*/
    public EdgeIfc addEdge( Vertex start,  Vertex end )
    {
	  Neighbor e = new Neighbor( end );
        addEdge( start, e );
        return e;
    }

        
    public void addVertex( Vertex v ) {
        vertices.add( v );
    }
   
    public void addEdge( Vertex start,  Neighbor theNeighbor ) {
        start.addEdge( theNeighbor );
    }
    
    // Finds a vertex given its name in the vertices list
    public  /*@pure@*/ Vertex findsVertex( String theName )
      {
        Vertex theVertex = null;

        // if we are dealing with the root
        if ( theName==null )
        {
            return null;
        }

        for(VertexIter vxiter = getVertices( ); vxiter.hasNext( ); )
        {
            theVertex = vxiter.next( );
            if ( theName.equals( theVertex.getName( ) ) )
            {
                return theVertex;
            }
        }

        return theVertex;
    }
    /*@ ensures \result != null; @*/
    /*@ assignable \nothing; @*/
    public VertexIter getVertices( ) 
    {
        return new VertexIter( ) 
        {
                private Iterator iter = vertices.iterator( );
                public Vertex next( ) 
                { 
                    return (Vertex)iter.next( ); 
                }
                public boolean hasNext( ) 
                { 
                    return iter.hasNext( ); 
                }
            };
    }

    
    public void display( ) 
    {
        System.out.println( "******************************************" );
        System.out.println( "Vertices " );
        for ( VertexIter vxiter = getVertices( ); vxiter.hasNext( ) ; )
        {
            vxiter.next( ).display( );
        }
        System.out.println( "******************************************" );

    }
      
}
