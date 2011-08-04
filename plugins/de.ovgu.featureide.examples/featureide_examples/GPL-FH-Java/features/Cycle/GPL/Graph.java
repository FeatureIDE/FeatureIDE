package GPL;

import java.lang.Integer;

// Cycle checking, Edge-Neighbor implementation
  
// *************************************************************************
   
public class Graph {

    // Executes Cycle Checking
    public void run( Vertex s )
     {
        System.out.println( "Cycle? " + CycleCheck() );
        original( s );
    }
              
    public boolean CycleCheck() {
        CycleWorkSpace c = new CycleWorkSpace( isDirected );
        GraphSearch( c );
        return c.AnyCycles;
    }
}
