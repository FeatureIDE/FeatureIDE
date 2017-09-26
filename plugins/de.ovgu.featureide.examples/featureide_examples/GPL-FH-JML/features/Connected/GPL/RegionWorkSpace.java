package GPL;

import java.util.LinkedList;

// *****************************************************************
   
public class RegionWorkSpace extends  WorkSpace {

	/*@ spec_public  @*/int counter;
    
    /*@ensures counter == 0;@*/
	/*@assignable counter; @*/
    public RegionWorkSpace( ) 
    {
        counter = 0;
    }
    /*@requires v != null; @*/
    /*@ensures v.componentNumber == -1; @*/
    /*@assignable \nothing; @*/
    public void init_vertex( Vertex v ) 
    {
        v.componentNumber = -1;
    }
    /*@requires v != null;  @*/
    /*@ensures v.componenNumber == counter;  @*/
    /*@assignable \nothing; @*/
    public void postVisitAction( Vertex v ) 
    {
        v.componentNumber = counter;
    }
    
    /*@ensures counter = \old(counter)+1;  @*/
    /*@assignable counter; @*/
    public void nextRegionAction( Vertex v ) 
    {
        counter ++;
    }
}
