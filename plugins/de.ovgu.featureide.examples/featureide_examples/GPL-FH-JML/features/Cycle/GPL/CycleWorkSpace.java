package GPL;

import java.lang.Integer;
import java.util.LinkedList;

// *************************************************************************
   
public class CycleWorkSpace extends  WorkSpace {

    public /*@ spec_public @*/ boolean AnyCycles;
    public /*@ spec_public @*/ int     counter;
    public /*@ spec_public @*/ boolean isDirected;
      
    public /*@ spec_public @*/  LinkedList vertices;
     /*@ spec_public @*/ static final int WHITE = 0;
    public/*@ spec_public @*/ static final int GRAY  = 1;
    public /*@ spec_public @*/ static final int BLACK = 2;
            
    /*@ensures AnyCycles == false && counter == 0 && isDirected == UnDir;@*/
    public CycleWorkSpace( boolean UnDir ) {
        AnyCycles = false;
        counter   = 0;
        isDirected = UnDir;
    }
    /*@requires v != null; @*/
    /*@ensures v.VertexCycle == Integer.MAX_VALUE;@*/
    /*@ensures v.VertexColor == WHITE;@*/
    public void init_vertex( Vertex v ) 
      {
        v.VertexCycle = Integer.MAX_VALUE;
        v.VertexColor = WHITE; // initialize to white color
    }

    /*@requires v != null; @*/
    /*@ensures (v.visited != true) ==> (v.VertexCycle == \old(v.VertexCycle)+1 && v.VertexColor == GRAY);@*/
    public void preVisitAction( Vertex v ) {
        
        // This assigns the values on the way in
        if ( v.visited!=true ) 
        { // if it has not been visited then set the
            // VertexCycle accordingly
            v.VertexCycle = counter++;
            v.VertexColor = GRAY; // we make the vertex gray
        }
    }
    /*@requires v != null; @*/
    /*@ensures v.VertexColor == BLACK; @*/
    /*@ensures counter  == \old(counter)-1;@*/
    public void postVisitAction( Vertex v ) 
      {
        v.VertexColor = BLACK; // we are done visiting so make it black
        counter--;
    } // of postVisitAction

    

    /*@requires vsource != null && vtarget != null; @*/
    /*@ensures isDirected ==>((vsource.VertexColor == GRAY) && (vtarget.VertexColor == GRAY)==>AnyCicles == true);  @*/
    /*@ensures !isDirected ==>((vsource.VertexColor == GRAY) && (vtarget.VertexColor == GRAY && (vsource.VertexCycle != vtarget.VertexCycle+1))==>AnyCicles == true);  @*/
    public void checkNeighborAction( Vertex vsource, 
                     Vertex vtarget ) 
      {
        // if the graph is directed is enough to check that the source node
        // is gray and the adyacent is gray also to find a cycle
        // if the graph is undirected we need to check that the adyacent is not
        // the father, if it is the father the difference in the VertexCount is
        // only one.                                   
        if ( isDirected )
        {
            if ( ( vsource.VertexColor == GRAY ) && ( vtarget.VertexColor == GRAY ) ) 
              {
                AnyCycles = true;
            }
        }
        else
        { // undirected case
            if ( ( vsource.VertexColor == GRAY ) && ( vtarget.VertexColor == GRAY ) 
                 && vsource.VertexCycle != vtarget.VertexCycle+1 ) 
              {
                AnyCycles = true;
            }
        }
        
    } // of checkNeighboor
   
}
