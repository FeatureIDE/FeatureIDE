//layer Transpose;

//dja: Added for performance improvement
//import java.util.HashMap;
//import java.util.Map;

using System.Collections;
using System.Collections.Generic;
// *********************************************************

public class Graph {//refines

    public  Graph ComputeTranspose( Graph the_graph )
   {
        int i;
        string theName;

        //dja: Added for performance improvement
        Dictionary<string, Vertex> newVertices = new Dictionary<string, Vertex>();

        // Creating the new Graph
        Graph newGraph = new  Graph();

        // Creates and Adds the vertices with the same name
        for ( Iterator<Vertex> vxiter = GetVertices(); vxiter.hasNext(); )
        {
            theName = vxiter.next().GetName();
            //dja: changes for performance improvement
            Vertex v = new  Vertex( ).assignName( theName );
//            newGraph.AddVertex( new  Vertex().assignName( theName ) );
            newGraph.AddVertex( v );

            //dja: Added for performance improvement
            newVertices.Add( theName, v );
        }

        Vertex theVertex, newVertex;
        Vertex theNeighbor;
        Vertex newAdjacent;
        EdgeIfc newEdge;

        // Adds the transposed edges
        // dja: Added line below for performance improvements
        Iterator<Vertex> newvxiter = newGraph.GetVertices( );
        for ( Iterator<Vertex> vxiter = GetVertices(); vxiter.hasNext(); )
        {
            // theVertex is the original source vertex
            // the newAdjacent is the reference in the newGraph to theVertex
            theVertex = vxiter.next();

            // dja: performance improvement fix
            // newAdjacent = newGraph.findsVertex( theVertex.GetName() );
            newAdjacent = newvxiter.next( );

            for( Iterator<Vertex> neighbors = theVertex.GetNeighbors(); neighbors.hasNext(); )
            {
                // Gets the neighbor object
                theNeighbor = neighbors.next();

                // the new Vertex is the vertex that was adjacent to theVertex
                // but now in the new graph
                // dja: performance improvement fix
                // newVertex = newGraph.findsVertex( theNeighbor.GetName() );
                newVertex = ( Vertex ) newVertices[theNeighbor.GetName( )];

                // Creates a new Edge object and adjusts the adornments
                newEdge = newGraph.AddEdge( newVertex, newAdjacent );
                //newEdge.adjustAdorns( theNeighbor.edge );

                // Adds the new Neighbor object with the newly formed edge
                // newNeighbor = new $TEqn.Neighbor(newAdjacent, newEdge);
                // (newVertex.neighbors).Add(newNeighbor);

            } // all adjacentNeighbors
        } // all the vertices

        return newGraph;

    } // of ComputeTranspose

}
