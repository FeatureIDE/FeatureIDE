//layer Undirected;

//import java.util.Iterator;
using System.Collections;
using System.Collections.Generic;

// ************************************************************

public class Vertex : EdgeIfc, NeighborIfc
{
    public List<Vertex> adjacentVertices;
    public string name;

    public Vertex( )
    {
        VertexConstructor( );
    }

    public void VertexConstructor( )
    {
        name      = null;
        adjacentVertices = new List<Vertex>();
    }

    public  Vertex assignName( string name )
    {
        this.name = name;
        return ( Vertex ) this;
    }

    public Iterator<Vertex> GetNeighbors( )
    {
        return new Iterator<Vertex>(adjacentVertices.GetEnumerator());
    }

    public void display() {
        int s = adjacentVertices.Count;
        int i;

        System.Console.Out.Write( "Vertex " + name + " connected to: " );
        for ( i=0; i<s; i++ )
            System.Console.Out.Write( ( ( Vertex ) adjacentVertices[i] ).name
                                                + ", " );
        System.Console.Out.WriteLine();
    }
//--------------------
// differences
//--------------------

    public void AddAdjacent( Vertex n ) {
        adjacentVertices.Add( n );
    }

    public void adjustAdorns( Vertex the_vertex, int index )
      {}
    public List<Vertex> GetNeighborsObj( )
    {
      return adjacentVertices;
    }

    public Iterator<EdgeIfc> GetEdges( ) {
        return new Iterator<EdgeIfc>(adjacentVertices.GetEnumerator());
    }
    public string GetName( )
    {
        return this.name;
    }

//--------------------
// from EdgeIfc
//--------------------

    public Vertex GetStart( ) { return null; }
    public Vertex GetEnd( ) { return null; }

    public void setWeight( int weight ){}
    public int GetWeight() { return 0; }

    public Vertex GetOtherVertex( Vertex vertex )
    {
        return this;
    }



    public void adjustAdorns( EdgeIfc the_edge )
    {
    }


}
