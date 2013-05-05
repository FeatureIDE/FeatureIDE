package GPL;

import java.util.LinkedList;

// *************************************************************************
   
public class Neighbor {
    public /*@spec_public@*/  Vertex end;
    public /*@spec_public@*/ Edge edge;
        
    /*@ensures end == null && edge == null;@*/
    public Neighbor() {
        end = null;
        edge = null;
    }
    /*@requires v != null && e != null;@*/
    /*@ensures end == v && edge == e;@*/  
    public Neighbor( Vertex v,  Edge e ) {
        end = v;
        edge = e;
    }

}
