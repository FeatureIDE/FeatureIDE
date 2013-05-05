package GPL;

import java.util.LinkedList;
import java.util.Collections;
import java.util.Comparator;

// ***********************************************************************
   
public class FinishTimeWorkSpace extends  WorkSpace {
	/*@spec_public@*/   int  FinishCounter;
 
    /*@ensures FinishCounter == 1;@*/
    public FinishTimeWorkSpace() {
        FinishCounter = 1;
    }

    /*@requires v != null;@*/
    /*@ensures !v.visited() ==> FinishCounter == \old(FinishCounter)+1;@*/
    public void preVisitAction( Vertex v )
      {
        if ( v.visited!=true )
            FinishCounter++;
    }
    /*@requires v != null;@*/
    /*@ensures v.finishTime == \old(FinishCounter)+1;@*/
    public void postVisitAction( Vertex v ) {
        v.finishTime = FinishCounter++;
    } // of postVisit
    
}
