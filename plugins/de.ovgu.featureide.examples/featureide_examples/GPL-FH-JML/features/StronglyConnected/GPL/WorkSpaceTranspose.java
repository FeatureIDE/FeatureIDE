package GPL;

import java.util.LinkedList;
import java.util.Collections;
import java.util.Comparator;

// of FinishTimeWorkSpace
   
  // DFS Transpose traversal
  // *************************************************************************
   
public class WorkSpaceTranspose extends  WorkSpace {
    // Strongly Connected Component Counter
	/*@spec_public@*/ int  SCCCounter;
    
    /*@ensures SCCCounter == 0;@*/
    public WorkSpaceTranspose()
	{
        SCCCounter = 0;
    }
    /*@requires v != null;@*/
    /*@ensures !v.visited() ==> v.strongComponentNumber == SCCCounter;@*/   
    public void preVisitAction( Vertex v )
    {
        if ( v.visited!=true ) 
          {
            v.strongComponentNumber = SCCCounter;
        }
        ;
    }
   
    /*@ensures SCCCounter == \old(SCCCounter)+1;@*/ 
    public void nextRegionAction( Vertex v ) 
    {
        SCCCounter++;
    }

}
