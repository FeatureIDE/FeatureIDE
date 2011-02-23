//layer Connected;

// *****************************************************************
   
public class RegionWorkSpace :  WorkSpace 
{
    int counter;

    public RegionWorkSpace( ) 
    {
        counter = 0;
    }

    public override void init_vertex( Vertex v ) 
    {
        v.componentNumber = -1;
    }
      
    public override void postVisitAction( Vertex v ) 
    {
        v.componentNumber = counter;
    }

    public override void nextRegionAction( Vertex v ) 
    {
        counter ++;
    }
}
