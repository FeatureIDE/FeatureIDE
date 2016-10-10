//layer Cycle;

//import java.lang.Integer;

// *************************************************************************
   
public class Vertex {//refines
    public int VertexCycle;
    public int VertexColor; // white ->0, gray ->1, black->2
      
    public virtual void display() {
        System.Console.Out.Write( " VertexCycle# " + VertexCycle + " " );
        original();
    }
}
