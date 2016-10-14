//layer StronglyConnected;

using System.Collections;
//import java.util.Collections;
//import java.util.Comparator;

// ***********************************************************************
   
public class FinishTimeWorkSpace :  WorkSpace {
    int FinishCounter;
 
    public FinishTimeWorkSpace() {
        FinishCounter = 1;
    }

    public override void preVisitAction( Vertex v )
      {
        if ( v.visited!=true )
            FinishCounter++;
    }

    public override void postVisitAction( Vertex v ) {
        v.finishTime = FinishCounter++;
    } // of postVisit
    
}
