//layer Directed;

using System.Collections;
using System.Collections.Generic;
//import java.util.Iterator;

// of graph

  // ***********************************************************************

public class Vertex {

    // dja: changed neighbors and name to public
    public List<Neighbor> neighbors;

    public string name;

    public string GetName() { return name; }

    public Vertex() {
        VertexConstructor();
    }

    public void VertexConstructor() {
        name      = null;
        neighbors = new List<Neighbor>();
    }

    public  Vertex assignName( string name ) {
        this.name = name;
        return ( Vertex ) this;
    }

    public void AddNeighbor( Neighbor n ) {
        neighbors.Add( n );
    }

    public Iterator<Vertex> GetNeighbors() {
        return new Iterator<Vertex, Neighbor>(neighbors.GetEnumerator(), TransformNeighborToEnd);
    }
    public static Vertex TransformNeighborToEnd(Neighbor val) {
    	// should be a Lambda Method in C# 3.0
        return val.end;
    }
    public Iterator<EdgeIfc> GetEdges() {
        return new Iterator<EdgeIfc, Neighbor>(neighbors.GetEnumerator(), TransformNeighborToEdge);
    }
    public static EdgeIfc TransformNeighborToEdge(Neighbor val) {
    	// should be a Lambda Method in C# 3.0
        return val.edge;
    }

    public void display() {
        System.Console.Out.Write( " Node " + GetName() + " connected to: " );

        for(Iterator<Vertex> vxiter = GetNeighbors(); vxiter.hasNext(); )
         {
            Vertex v = vxiter.next();
            System.Console.Out.Write( v.GetName() + ", " );
        }

        System.Console.Out.WriteLine();
    }
}
