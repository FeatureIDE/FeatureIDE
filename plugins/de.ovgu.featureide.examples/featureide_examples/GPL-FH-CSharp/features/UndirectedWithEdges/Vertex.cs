//layer Undirected;

//import java.util.Iterator;
using System.Collections;
using System.Collections.Generic;

// *********************************************************************

public class Vertex 
{
    public List<Neighbor> neighbors;
    public string name;

    public Vertex( ) 
    {
        VertexConstructor( );
    }

    public void VertexConstructor( ) 
    {
        name      = null;
        neighbors = new List<Neighbor>( );
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
 	  return neighbors;
    }


    public Iterator<Vertex> GetNeighbors() {
        return new Iterator<Vertex, Neighbor>(neighbors.GetEnumerator(), TransformNeighborToEnd);
    }
    public static Vertex TransformNeighborToEnd(Neighbor val) {
        // should be a Lambda Method in C# 3.0
        return val.end;
    }
    public void display( ) 
    {
        System.Console.Out.Write( " Node " + name + " connected to: " );

        for ( Iterator<Vertex> vxiter = GetNeighbors( ); vxiter.hasNext( ); )
        {
            System.Console.Out.Write( vxiter.next().GetName() + ", " );
        }

        System.Console.Out.WriteLine( );
    }      
//--------------------
// differences
//--------------------

    public void AddNeighbor( Neighbor n ) 
    {
        neighbors.Add( n );
    }

        public Iterator<EdgeIfc> GetEdges() {
        return new Iterator<EdgeIfc, Neighbor>(neighbors.GetEnumerator(), TransformNeighborToEdge);
    }
    public static EdgeIfc TransformNeighborToEdge(Neighbor val) {
        // should be a Lambda Method in C# 3.0
        return val.edge;
    }
}
