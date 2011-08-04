package GPL;

import java.util.LinkedList;

// *************************************************************************
   
public class WorkSpace 
{ // supply template actions
    public void init_vertex( Vertex v ) {}
    public void preVisitAction( Vertex v ) {}
    public void postVisitAction( Vertex v ) {}
    public void nextRegionAction( Vertex v ) {}
    public void checkNeighborAction( Vertex vsource, 
     Vertex vtarget ) {}
}
