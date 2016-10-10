//layer Directed;

//import java.util.Iterator;
//import java.util.LinkedList;
// of Graph
   
  // *************************************************************************   
   using System.Collections;
   using System.Collections.Generic;
public class Vertex {
    public List<Vertex> adjacentNeighbors;
    public string name;
   
    public Vertex() {
        VertexConstructor();
    }
    public string GetName( ) 
    { 
        return name; 
    }

    public virtual void VertexConstructor() {
        name      = null;
        adjacentNeighbors = new List<Vertex>();
    }

    public  virtual Vertex assignName( string name ) {
        this.name = name;
        return ( Vertex ) this;
    }
   
    public virtual void AddEdge( Neighbor n ) {
        adjacentNeighbors.Add(n);
    }


    public virtual Iterator<Vertex> GetNeighbors( ) 
    {
        return new Iterator<Vertex>(adjacentNeighbors.GetEnumerator(), TransformToNeighbor);
    } 
    public static Vertex TransformToNeighbor (Vertex val) {
    	return ((Neighbor)val.Current).neighbor;
    }

    public virtual void adjustAdorns( Neighbor sourceNeighbor )
      {}
      
    public virtual void display() 
    {
        System.Console.Out.Write( "Node " + GetName( ) + " connected to: " );

        for(Vertex<Iterator> vxiter = GetNeighbors( ); vxiter.hasNext( ); )
         {
            Vertex v = vxiter.next( );
            System.Console.Out.Write( v.GetName( ) + ", " );
        }
        System.Console.Out.WriteLine( );
    }
}
