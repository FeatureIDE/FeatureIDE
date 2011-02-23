//layer StronglyConnected;

using System.Collections;
using System.Collections.Generic;

// Cormen's Textbook 23.5
// ***********************************************************************

public class Graph {//refines

    // Executes Strongly Connected Components
    public void run( Vertex s )
     {
          	System.Console.Out.WriteLine("StronglyConnected");
        Graph gaux = StrongComponents();
//        Graph.stopProfile();
        gaux.display();
//        Graph.resumeProfile();
        original( s );
    }

    public  Graph StrongComponents() {

        FinishTimeWorkSpace FTWS = new FinishTimeWorkSpace();

        // 1. Computes the finishing times for each vertex
        GraphSearch( FTWS );

        // 2. Order in decreasing  & call DFS Transposal
        sortVertices(new VertexComparer());

        // 3. Compute the transpose of G
        // Done at layer transpose
        Graph gaux = ComputeTranspose( ( Graph )this );

        // 4. Traverse the transpose G
        WorkSpaceTranspose WST = new WorkSpaceTranspose();
        gaux.GraphSearch( WST );

        return gaux;
    } // of Strong Components
	public class VertexComparer : IComparer<Vertex> {
	    public int Compare(Vertex v1, Vertex v2) {
            if ( v1.finishTime > v2.finishTime )
                return -1;
            if ( v1.finishTime == v2.finishTime )
                return 0;
            return 1;
	    }
	}
}
