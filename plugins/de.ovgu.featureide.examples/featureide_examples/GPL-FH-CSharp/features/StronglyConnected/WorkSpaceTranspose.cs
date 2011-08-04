//layer StronglyConnected;

using System.Collections;
//import java.util.Collections;
//import java.util.Comparator;

// of FinishTimeWorkSpace
   
  // DFS Transpose traversal
  // *************************************************************************
   
public class WorkSpaceTranspose :  WorkSpace {
    // Strongly Connected Component Counter
    int SCCCounter;
        
    public WorkSpaceTranspose()
	{
        SCCCounter = 0;
    }
        
    public override void preVisitAction( Vertex v )
    {
        if ( v.visited!=true ) 
          {
            v.strongComponentNumber = SCCCounter;
        }
        ;
    }

    public override void nextRegionAction( Vertex v ) 
    {
        SCCCounter++;
    }

}
