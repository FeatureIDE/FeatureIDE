/*layer Cycle;

import java.lang.Integer;
*/
// Cycle checking, Edge-Neighbor implementation
  
// *************************************************************************
   
public class Graph {//refines

    // Executes Cycle Checking
    public virtual void run( Vertex s )
     {
        System.Console.Out.WriteLine( "Cycle? " + CycleCheck() );
        original( s );
    }
              
    public virtual bool CycleCheck() {
        CycleWorkSpace c = new CycleWorkSpace( isDirected );
        GraphSearch( c );
        return c.AnyCycles;
    }
}
