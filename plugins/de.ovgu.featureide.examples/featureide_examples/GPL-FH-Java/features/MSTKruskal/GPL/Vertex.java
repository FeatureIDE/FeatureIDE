package GPL;

import java.lang.Integer;
import java.util.LinkedList;
import java.util.Collections;
import java.util.Comparator;

// of Graph

  // *************************************************************************

public class Vertex {
    public  Vertex representative;
    public LinkedList members;

    public void display() {
        if ( representative == null )
            System.out.print( "Rep null " );
        else
            System.out.print( " Rep " + representative.getName() + " " );
        original();
    }
}
