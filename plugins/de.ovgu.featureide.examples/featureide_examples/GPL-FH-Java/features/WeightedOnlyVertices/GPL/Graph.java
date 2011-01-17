package GPL;

import java.util.LinkedList;

// ************************************************************
 
public class Graph {
    // Adds an edge with weights
    public void addAnEdge( Vertex start,  Vertex end, int weight )
   {
        addEdge( start,end, weight );
    }
 
    public void addEdge( Vertex start,  Vertex end, int weight )
   {
        addEdge( start,end ); // adds the start and end as adjacent
        start.addWeight( weight ); // the direction layer takes care of that
                
        // if the graph is undirected you have to include 
        // the weight of the edge coming back
        if ( isDirected==false )
            end.addWeight( weight );
    }
    
    public void display() 
   {
        original();
    }

}
