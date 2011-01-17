package GPL;

import java.util.LinkedList;

// *************************************************************************
   
public class Neighbor {
    public  Vertex end;
    public  Edge edge;
        
    public Neighbor() {
        end = null;
        edge = null;
    }
        
    public Neighbor( Vertex v,  Edge e ) {
        end = v;
        edge = e;
    }

}
