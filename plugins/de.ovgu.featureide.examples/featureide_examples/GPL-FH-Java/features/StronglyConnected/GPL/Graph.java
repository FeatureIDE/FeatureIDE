package GPL;

import java.util.LinkedList;

// Cormen's Textbook 23.5
// ***********************************************************************

public class Graph {

    // Executes Strongly Connected Components
    public void run( Vertex s )
     {
          	System.out.println("StronglyConnected");
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
        sortVertices(
         new Comparator() {
            public int compare( Object o1, Object o2 )
                {
                Vertex v1 = ( Vertex )o1;
                Vertex v2 = ( Vertex )o2;

                if ( v1.finishTime > v2.finishTime )
                    return -1;

                if ( v1.finishTime == v2.finishTime )
                    return 0;
                return 1;
            }
        } );

        // 3. Compute the transpose of G
        // Done at layer transpose
        Graph gaux = ComputeTranspose( ( Graph )this );

        // 4. Traverse the transpose G
        WorkSpaceTranspose WST = new WorkSpaceTranspose();
        gaux.GraphSearch( WST );

        return gaux;

    } // of Strong Components

}
