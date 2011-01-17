package GPL;

import java.util.LinkedList;
import java.util.Collections;
import java.util.Comparator;

// of Graph

  // ***********************************************************************
   
public class Vertex {
    public int finishTime;
    public int strongComponentNumber;
      
    public void display() {
        System.out.print( " FinishTime -> " + finishTime + " SCCNo -> " 
                        + strongComponentNumber );
        original();
    }
}
