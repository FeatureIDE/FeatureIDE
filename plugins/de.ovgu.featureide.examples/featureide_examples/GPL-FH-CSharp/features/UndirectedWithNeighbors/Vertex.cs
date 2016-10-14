//layer Undirected;

using System.Collections;
using System.Collections.Generic;

  // **********************************************************************   
   
public class Vertex
    {
    public List<Neighbor> adjacentNeighbors;
    public string name;

    public Vertex() 
    {
        VertexConstructor();
    }
      
    public void VertexConstructor() 
    {
        name      = null;
        adjacentNeighbors = new List<Neighbor>();
    }

    public  Vertex assignName( string name ) 
    {
        this.name = name;
        return ( Vertex ) this;
    }

    public string GetName( )
    {
        return this.name;
    }
    
    public List<Neighbor> GetNeighborsObj( )
    {
 	  return adjacentNeighbors;
    }

    public Iterator<Vertex> GetNeighbors( )
    {
        return new Iterator<Vertex, Neighbor>(adjacentNeighbors.GetEnumerator(), TransformToNeighbor);
    }
	public Vertex TransformToNeighbor (Neighbor val){
		return val.neighbor;
	}
    public void display( ) 
    {
        System.Console.Out.Write( "Node " + name + " connected to: " );

        for ( Iterator<Vertex> vxiter = GetNeighbors( ); vxiter.hasNext( ); )
        {
            System.Console.Out.Write( vxiter.next( ).GetName( ) + ", " );
        }

        System.Console.Out.WriteLine();
    }
//--------------------
// differences
//--------------------

    public void AddEdge( Neighbor n ) 
    {
        adjacentNeighbors.Add( n );
    }

    public void adjustAdorns( Neighbor sourceNeighbor )
    {
    }

    public Iterator < EdgeIfc > GetEdges (){
	    return new Iterator < EdgeIfc, Neighbor > (adjacentNeighbors.GetEnumerator (), CastNeighborToEdgeIfc);
    }
    public static EdgeIfc CastNeighborToEdgeIfc(Neighbor val) {
        return val; //implicit upcast
    }
}
