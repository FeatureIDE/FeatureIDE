///layer Cycle;

//import java.lang.Integer;

// *************************************************************************
   
public class CycleWorkSpace :  WorkSpace {

    public bool AnyCycles;
    public int     counter;
    public bool isDirected;
      
    public static int WHITE = 0;
    public static int GRAY  = 1;
    public static int BLACK = 2;
            
    public CycleWorkSpace( bool UnDir ) {
        AnyCycles = false;
        counter   = 0;
        isDirected = UnDir;
    }

    public override void init_vertex( Vertex v ) 
      {
        v.VertexCycle = System.Int32.MaxValue;
        v.VertexColor = WHITE; // initialize to white color
    }

    public override void preVisitAction( Vertex v ) {
        
        // This assigns the values on the way in
        if ( v.visited!=true ) 
        { // if it has not been visited then set the
            // VertexCycle accordingly
            v.VertexCycle = counter++;
            v.VertexColor = GRAY; // we make the vertex gray
        }
    }

    public override void postVisitAction( Vertex v ) 
      {
        v.VertexColor = BLACK; // we are done visiting so make it black
        counter--;
    } // of postVisitAction

    public override void checkNeighborAction( Vertex vsource, 
                     Vertex vtarGet ) 
      {
        // if the graph is directed is enough to check that the source node
        // is gray and the adyacent is gray also to find a cycle
        // if the graph is undirected we need to check that the adyacent is not
        // the father, if it is the father the difference in the VertexCount is
        // only one.                                   
        if ( isDirected )
        {
            if ( ( vsource.VertexColor == GRAY ) && ( vtarGet.VertexColor == GRAY ) ) 
              {
                AnyCycles = true;
            }
        }
        else
        { // undirected case
            if ( ( vsource.VertexColor == GRAY ) && ( vtarGet.VertexColor == GRAY ) 
                 && vsource.VertexCycle != vtarGet.VertexCycle+1 ) 
              {
                AnyCycles = true;
            }
        }
        
    } // of checkNeighboor
   
}
