//layer MSTKruskal;

//import java.lang.Integer;
using System.Collections;
using System.Collections.Generic;
//import java.util.Collections;
//import java.util.Comparator;

// *************************************************************************

public class Graph {// refines

    // Executes MSTKruskal
    public void run( Vertex s )
     {
     	System.Console.Out.WriteLine("MSTKruskal");
        Graph gaux = Kruskal();
//        Graph.stopProfile();
        gaux.display();
//        Graph.resumeProfile();
        original( s );
    }

    public  Graph Kruskal() {

        // 1. A <- Empty set
        ArrayList A = new ArrayList();

        // 2. for each vertex v E V[G]
        // 3.    do Make-Set(v)

        for ( Iterator<Vertex> vxiter = GetVertices(); vxiter.hasNext(); )
        {
            Vertex v = vxiter.next();
            v.representative = v; // I am in my set
            v.members = new ArrayList(); // I have no members in my set
        }

        // 4. sort the edges of E by nondecreasing weight w
        // Creates the edges objects
        //int j;
        ArrayList Vneighbors = new ArrayList();
        //Vertex u;

        // Sort the Edges in non decreasing order
        sortEdges( new EdgeComparer());

        // 5. for each edge in the nondecresing order
        Vertex vaux, urep, vrep;

        for( Iterator<EdgeIfc> edgeiter = GetEdges(); edgeiter.hasNext(); )
        {
            // 6. if Find-Set(u)!=Find-Set(v)
            EdgeIfc e1 = edgeiter.next();
            Vertex u = e1.GetStart();
            Vertex v = e1.GetEnd();

            if ( ! ( v.representative.GetName() ).Equals( u.representative.GetName() ) )
              {
                // 7. A <- A U {(u,v)}
                A.Add( e1 );

                // 8. Union(u,v)
                urep = u.representative;
                vrep = v.representative;

                if ( ( urep.members ).Count > ( vrep.members ).Count )
                    { // we Add elements of v to u
                    for( int j=0; j< ( vrep.members ).Count; j++ )
                          {
                        vaux = ( Vertex ) ( vrep.members[j]);
                        vaux.representative = urep;
                        ( urep.members ).Add( vaux );
                    }
                    v.representative = urep;
                    vrep.representative = urep;
                    ( urep.members ).Add( v );
                    if ( !v.Equals( vrep ) )
                        ( urep.members ).Add( vrep );
                    ( vrep.members ).Clear();
                }
                else
                     { // we Add elements of u to v
                    for( int j=0; j< ( urep.members ).Count; j++ )
                           {
                        vaux = ( Vertex ) ( urep.members[j] );
                        vaux.representative = vrep;
                        ( vrep.members ).Add( vaux );
                    }
                    u.representative = vrep;
                    urep.representative = vrep;
                    ( vrep.members ).Add( u );
                    if ( !u.Equals( urep ) )
                        ( vrep.members ).Add( urep );
                    ( urep.members ).Clear();

                } // else

            } // of if

        } // of for numedges

        // 9. return A
        // Creates the new Graph that contains the SSSP
        string theName;
        Graph newGraph = new  Graph();

        // Creates and Adds the vertices with the same name
        for ( Iterator<Vertex> vxiter = GetVertices(); vxiter.hasNext(); )
      {
            theName = vxiter.next().GetName();
            newGraph.AddVertex( new  Vertex().assignName( theName ) );
        }

        // Creates the edges from the NewGraph
        Vertex theStart, theEnd;
        Vertex theNewStart, theNewEnd;
        EdgeIfc   theEdge;

        // For each edge in A we find its two vertices
        // make an edge for the new graph from with the correspoding
        // new two vertices
        for( int i=0; i<A.Count; i++ )
       {
            // theEdge with its two vertices
            theEdge = ( Edge )A[i] ;
            theStart = theEdge.GetStart();
            theEnd = theEdge.GetEnd();

            // Find the references in the new Graph
            theNewStart = newGraph.findsVertex( theStart.GetName() );
            theNewEnd = newGraph.findsVertex( theEnd.GetName() );

            // Creates the new edge with new start and end vertices
            // in the newGraph
            // and ajusts the adorns based on the old edge
            // Adds the new edge to the newGraph
            // dja - the fix below fixes a bug where the proper adjust adorns Gets called
//            EdgeIfc theNewEdge = newGraph.AddEdge( theNewStart, theNewEnd );
//            theNewEdge.adjustAdorns( theEdge );
            Edge theNewEdge = ( Edge ) newGraph.AddEdge( theNewStart, theNewEnd );
            theNewEdge.adjustAdorns( ( Edge )  theEdge );
        }
        return newGraph;

    } // kruskal
    public class EdgeComparer : IComparer<EdgeIfc> {
        public int Compare(EdgeIfc e1, EdgeIfc e2) {
            if (e1.GetWeight() < e2.GetWeight())
                return -1;
            if (e1.GetWeight() == e2.GetWeight())
                return 0;
            return 1;
        }
    }
}
