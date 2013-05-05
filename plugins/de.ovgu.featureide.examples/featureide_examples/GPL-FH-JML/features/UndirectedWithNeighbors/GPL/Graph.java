package GPL;

import java.util.Iterator;
import java.util.LinkedList;

//dja: add for performance reasons
import java.util.HashMap;
import java.util.Map;


// *************************************************************************
   
public class Graph 
{
    public /*@spec_public@*/  LinkedList vertices;
    public /*@spec_public@*/  static boolean isDirected = false;
      
    //dja: add for performance reasons
    private /*@spec_public@*/  Map verticesMap;

    /*@ ensures vertices != null && verticesMap != null;@*/
   
    public Graph( ) 
    {
        vertices = new LinkedList();

	  //dja: add for performance reasons
        verticesMap = new HashMap( );

    }
 
    // Fall back method that stops the execution of programs
    public void run( Vertex s )
    {
    }

    // Adds an edge without weights if Weighted layer is not present
	/*@ requires start != null && theNeighbor != null; @*/
	/*@ ensures \result.getOtherVertex(start)==theNeighbor && \result.getOtherVertex(theNeighbor)==start; @*/
    public void addEdge( Vertex start,   Neighbor theNeighbor ) 
    {
        start.addEdge( theNeighbor );
        Vertex end = theNeighbor.neighbor;
        end.addEdge( new  Neighbor( start ) );
    }

        
    public void addVertex( Vertex v ) 
    {
        vertices.add( v );

	  //dja: add for performance reasons
	  verticesMap.put( v.name, v );
    }
   
    // Finds a vertex given its name in the vertices list
    public  /*@pure@*/ Vertex findsVertex( String theName )
    {
        Vertex theVertex;
        
        // if we are dealing with the root
        if ( theName == null )
            return null;

	  //dja: removed for performance reasons
//        for( VertexIter vxiter = getVertices( ); vxiter.hasNext( ); )
//        {
//            theVertex = vxiter.next( );
//            if ( theName.equals( theVertex.getName( ) ) )
//            {
//               return theVertex;
//            }
//        }
//        return null;

	  //dja: add for performance reasons
	  return ( Vertex ) verticesMap.get( theName );

    }
    /*@ ensures \result != null; @*/
    public VertexIter getVertices( ) 
    {
        return new VertexIter( ) 
        {
            private Iterator iter = vertices.iterator( );
            public Vertex next( ) 
            { 
                return ( Vertex )iter.next( ); 
            }
            public boolean hasNext( ) 
            { 
                return iter.hasNext(); 
            }
        };
    }

    // Finds an Edge given both of its vertices
    public  /*@pure@*/ EdgeIfc findsEdge( Vertex theSource,
                    Vertex theTarget )
       {
	  //dja: performance improvement
        //for( VertexIter vertexiter = getVertices(); vertexiter.hasNext(); )
        // {
	  //	Vertex v1 = vertexiter.next( );
	  //	for( EdgeIter edgeiter = v1.getEdges(); edgeiter.hasNext(); )
        //    {
	  //          EdgeIfc theEdge = edgeiter.next();
	  //		Vertex v2 = theEdge.getOtherVertex( v1 );
        //	      if ( ( v1.getName().equals( theSource.getName() ) &&
        //    	       v2.getName().equals( theTarget.getName() ) ) ||
        //         	     ( v1.getName().equals( theTarget.getName() ) &&
        //          	 v2.getName().equals( theSource.getName() ) ) )
        //        	return theEdge;
        //    }
        //}
		Vertex v1 = theSource;
		for( EdgeIter edgeiter = v1.getEdges(); edgeiter.hasNext(); )
            {
	            EdgeIfc theEdge = edgeiter.next();
			Vertex v2 = theEdge.getOtherVertex( v1 );
      	      if ( ( v1.getName().equals( theSource.getName() ) &&
            	       v2.getName().equals( theTarget.getName() ) ) ||
                 	     ( v1.getName().equals( theTarget.getName() ) &&
                  	 v2.getName().equals( theSource.getName() ) ) )
                	return theEdge;
            }
        return null;
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

    // Adds an edge without weights if Weighted layer is not present
	/*@ requires v1 != null && v2 != null; @*/
	/*@ ensures \result.getOtherVertex(v1)==v2 && \result.getOtherVertex(v2)==v1; @*/
    public EdgeIfc addEdge( Vertex start,  Vertex end )
      {
	  Neighbor e = new Neighbor( end );
        addEdge( start, e );
        return e;
    }
      
}
