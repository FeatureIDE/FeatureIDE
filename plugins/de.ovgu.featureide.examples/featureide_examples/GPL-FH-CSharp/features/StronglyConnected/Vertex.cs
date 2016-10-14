//layer StronglyConnected;

using System.Collections;
//import java.util.Collections;
//import java.util.Comparator;

// of Graph

  // ***********************************************************************
   
public class Vertex {//refines
    public int finishTime;
    public int strongComponentNumber;
      
    public void display() {
        System.Console.Out.Write( " FinishTime -> " + finishTime + " SCCNo -> " 
                        + strongComponentNumber );
        original();
    }
}
