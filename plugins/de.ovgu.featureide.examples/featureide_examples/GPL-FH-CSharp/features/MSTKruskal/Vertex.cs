//layer MSTKruskal;

//import java.lang.Integer;
using System.Collections;
//import java.util.Collections;
//import java.util.Comparator;

// of Graph

  // *************************************************************************

public class Vertex {//refines
    public  Vertex representative;
    public ArrayList members;

    public void display() {
        if ( representative == null )
            System.Console.Out.Write( "Rep null " );
        else
            System.Console.Out.Write( " Rep " + representative.GetName() + " " );
        original();
    }
}
