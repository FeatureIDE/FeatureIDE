package GPL;

import java.util.LinkedList;

// ************************************************************
 
public class Graph {
    // Adds an edge with weights
	/*@requires start != null && end != null && weight != null;@*/
	/*@ensures findsEdge(start,end) != null && findsEdge(start, end).getWeight()==weight;@*/
    public void addAnEdge( Vertex start,  Vertex end, int weight )
   {
        addEdge( start,end, weight );
    }
    /*@requires start != null && end != null ;@*/
	/*@ ensures \result.getOtherVertex(start)==end && \result.getOtherVertex(end)==start; @*/
    /*@ensures !isDirected ==> (theNeighbor.neighbor.getWeight()==theNeighbor.weight);@*/
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
