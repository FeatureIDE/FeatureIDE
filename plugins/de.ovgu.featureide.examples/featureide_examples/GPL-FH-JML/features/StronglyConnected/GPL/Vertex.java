package GPL;

import java.util.LinkedList;
import java.util.Collections;
import java.util.Comparator;

// of Graph

  // ***********************************************************************
   
public class Vertex {
    public /*@spec_public@*/ int finishTime;
    public /*@spec_public@*/ int  strongComponentNumber;
      
    public void display() {
        System.out.print( " FinishTime -> " + finishTime + " SCCNo -> " 
                        + strongComponentNumber );
        original();
    }
}
