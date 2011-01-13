package GPL;

import java.util.LinkedList;
import java.util.Iterator;

// of graph

  // ***********************************************************************

public class Vertex {

    // dja: changed neighbors and name to public
    public LinkedList neighbors;

    public String name;

    public String getName() { return name; }

    public Vertex() {
        VertexConstructor();
    }

    public void VertexConstructor() {
        name      = null;
        neighbors = new LinkedList();
    }

    public  Vertex assignName( String name ) {
        this.name = name;
        return ( Vertex ) this;
    }

    public void addNeighbor( Neighbor n ) {
        neighbors.add( n );
    }

    public VertexIter getNeighbors() {
        return new VertexIter() {
                private Iterator iter = neighbors.iterator();
                public Vertex next() { return ((Neighbor)iter.next()).end; }
                public boolean hasNext() { return iter.hasNext(); }
            };
    }

    public EdgeIter getEdges()
    {
        return new EdgeIter()
            {
                private Iterator iter = neighbors.iterator();
                /* dja: changed to fix compile error */
//                public EdgeIfc next() { return ((EdgeIfc)  iter.next()).edge; }
                public EdgeIfc next( ) 
                { 
                  return ( ( EdgeIfc ) ( ( Neighbor ) iter.next( ) ).edge ); 
                }
                public boolean hasNext() { return iter.hasNext(); }
            };
    }

    public void display() {
        System.out.print( " Node " + getName() + " connected to: " );

        for(VertexIter vxiter = getNeighbors(); vxiter.hasNext(); )
         {
            Vertex v = vxiter.next();
            System.out.print( v.getName() + ", " );
        }

        System.out.println();
    }
}
