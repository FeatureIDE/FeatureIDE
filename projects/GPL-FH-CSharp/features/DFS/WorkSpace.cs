/*layer DFS;
  // *************************************************************************
  */ 
public class WorkSpace 
{ // supply template actions
    public virtual void init_vertex( Vertex v ) {}
    public virtual void preVisitAction( Vertex v ) {}
    public virtual void postVisitAction( Vertex v ) {}
    public virtual void nextRegionAction( Vertex v ) {}
    public virtual void checkNeighborAction( Vertex vsource, 
                       Vertex vtarGet ) {}
}
