package GPL;

import java.util.Iterator;
import java.util.LinkedList;
// of Graph
   
  // *************************************************************************   
   
public class Vertex {
    public LinkedList adjacentNeighbors;
    public String name;
   
    public Vertex() {
        VertexConstructor();
    }
    public String getName( ) 
    { 
        return name; 
    }

    public void VertexConstructor() {
        name      = null;
        adjacentNeighbors = new LinkedList();
    }

    public  Vertex assignName( String name ) {
        this.name = name;
        return ( Vertex ) this;
    }
   
    public void addEdge( Neighbor n ) {
        adjacentNeighbors.add( n );
    }


    public VertexIter getNeighbors( ) 
    {
        return new VertexIter( ) 
        {
            private Iterator iter = adjacentNeighbors.iterator( );
            public Vertex next( ) 
            { 
               return ( ( Neighbor )iter.next( ) ).neighbor; 
            }

            public boolean hasNext( ) 
            {
               return iter.hasNext( ); 
            }
        };
    }

    public void adjustAdorns( Neighbor sourceNeighbor )
      {}
      
    public void display() 
    {
        System.out.print( "Node " + getName( ) + " connected to: " );

        for(VertexIter vxiter = getNeighbors( ); vxiter.hasNext( ); )
         {
            Vertex v = vxiter.next( );
            System.out.print( v.getName( ) + ", " );
        }
        System.out.println( );
    }
}
