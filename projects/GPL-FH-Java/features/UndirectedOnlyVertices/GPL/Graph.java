package GPL;

import java.util.Iterator;
import java.util.LinkedList;

//dja: add for performance reasons
import java.util.HashMap;
import java.util.Map;

// ************************************************************

public class Graph
{
    public LinkedList vertices;
    public static final boolean isDirected = false;
    //dja: add for performance reasons
    private Map verticesMap;


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
    public void addAnEdge( Vertex start,  Vertex end, int weight )
    {
        addEdge( start,end );
    }

    // Adds and edge by setting start as adjacent to end and
    // viceversa
    public EdgeIfc addEdge( Vertex start,  Vertex end )
    {
        start.addAdjacent( end );
        end.addAdjacent( start );
        return ( EdgeIfc ) start;
    }

     // Adds an edge without weights if Weighted layer is not present
 //   public void addEdge( Vertex start,   NeighborIfc theNeighbor )
   // {
     //   addEdge( Vertex start,  ( Vertex ) theNeighbor )
   // }



    public void addVertex( Vertex v )
    {
        vertices.add( v );

	  //dja: add for performance reasons
	  verticesMap.put( v.name, v );
    }

    // Finds a vertex given its name in the vertices list
    public  Vertex findsVertex( String theName )
      {
        int i=0;
        Vertex theVertex;

        // if we are dealing with the root
        if ( theName == null )
            return null;

	  //dja: removed for performance reasons
//        for( i=0; i<vertices.size(); i++ )
//        {
//            theVertex = ( Vertex )vertices.get( i );
//            if ( theName.equals( theVertex.name ) )
//                return theVertex;
//        }
//        return null;

	  //dja: add for performance reasons
	  return ( Vertex ) verticesMap.get( theName );
    }

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
                    return iter.hasNext( );
                }
        };
    }

    public void display() {
        int s = vertices.size();
        int i;

        System.out.println( "******************************************" );
        System.out.println( "Vertices " );
        for ( i=0; i<s; i++ )
            ( ( Vertex ) vertices.get( i ) ).display();
        System.out.println( "******************************************" );

    }
   public  EdgeIfc findsEdge( Vertex theSource,
                    Vertex theTarget )
       {
        //dja: performance improvement
//        for( VertexIter vertexiter = getVertices(); vertexiter.hasNext(); )
//         {
//        Vertex v1 = vertexiter.next( );
//        for( EdgeIter edgeiter = v1.getEdges(); edgeiter.hasNext(); )
//            {
//                EdgeIfc theEdge = edgeiter.next();
//            Vertex v2 = theEdge.getOtherVertex( v1 );
//              if ( ( v1.getName().equals( theSource.getName() ) &&
//                       v2.getName().equals( theTarget.getName() ) ) ||
//                         ( v1.getName().equals( theTarget.getName() ) &&
//                     v2.getName().equals( theSource.getName() ) ) )
//                    return theEdge;
//            }
//        }
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

}
